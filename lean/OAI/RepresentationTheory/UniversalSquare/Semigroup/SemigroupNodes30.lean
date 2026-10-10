import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes28

namespace OAI

/-! Semigroup Nodes 30. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12540 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1902 sg2370

lemma sg12541 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1874 sg2411

lemma sg12542 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1901 sg2371

lemma sg12543 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1874 sg2412

lemma sg12544 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1874 sg2413

lemma sg12545 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1874 sg2414

lemma sg12546 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1874 sg2415

lemma sg12547 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1874 sg2416

lemma sg12548 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1903 sg2370

lemma sg12549 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1874 sg2417

lemma sg12550 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1903 sg2371

lemma sg12551 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1905 sg2370

lemma sg12552 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1417 sg3115

lemma sg12553 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1874 sg2418

lemma sg12554 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1874 sg2419

lemma sg12555 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1908 sg2370

lemma sg12556 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1417 sg3116

lemma sg12557 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1417 sg3117

lemma sg12558 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1874 sg2420

lemma sg12559 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1874 sg2421

lemma sg12560 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1907 sg2371

lemma sg12561 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1908 sg2371

lemma sg12562 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,4,4] := by
  exact rowSquare_join (by decide) sg1033 sg3722

lemma sg12563 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1874 sg2422

lemma sg12564 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1906 sg2372

lemma sg12565 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,3,2,2] := by
  exact rowSquare_join (by decide) sg1906 sg2373

lemma sg12566 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,1] := by
  exact rowSquare_join (by decide) sg1906 sg2374

lemma sg12567 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1874 sg2423

lemma sg12568 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1874 sg2424

lemma sg12569 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1901 sg2376

lemma sg12570 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1874 sg2426

lemma sg12571 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1875 sg2410

lemma sg12572 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1874 sg2427

lemma sg12573 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1901 sg2377

lemma sg12574 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1875 sg2413

lemma sg12575 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1874 sg2428

lemma sg12576 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1901 sg2378

lemma sg12577 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1901 sg2380

lemma sg12578 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1875 sg2417

lemma sg12579 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1903 sg2377

lemma sg12580 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1874 sg2429

lemma sg12581 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1901 sg2382

lemma sg12582 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1875 sg2419

lemma sg12583 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1903 sg2380

lemma sg12584 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1874 sg2430

lemma sg12585 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1874 sg2431

lemma sg12586 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1968 sg2291

lemma sg12587 : RowSquare [5,4,2,2,2,2,2,2,2,1,1] [7,5,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1492 sg2596

lemma sg12588 : RowSquare [5,4,2,2,2,2,2,2,2,1,1] [7,6,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1493 sg2596

lemma sg12589 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg4539

lemma sg12590 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,5] := by
  exact rowSquare_join (by decide) sg1033 sg3691

lemma sg12591 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1] [5,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1688 sg2314

lemma sg12592 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1,1,1,1] [7,7,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1877 sg2382

lemma sg12593 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,5] := by
  exact rowSquare_join (by decide) sg1001 sg3476

lemma sg12594 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg2287

lemma sg12595 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg2288

lemma sg12596 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg2291

lemma sg12597 : RowSquare [6,5,3,2,2,1,1,1,1,1,1,1] [4,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg2167

lemma sg12598 : RowSquare [6,6,2,2,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1754 sg2270

lemma sg12599 : RowSquare [6,6,2,2,1,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg2271

lemma sg12600 : RowSquare [6,6,2,2,1,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg2275

lemma sg12601 : RowSquare [6,6,2,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg2276

lemma sg12602 : RowSquare [6,6,2,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg2277

lemma sg12603 : RowSquare [6,6,3,2,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg2626

lemma sg12604 : RowSquare [6,6,3,2,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg2627

lemma sg12605 : RowSquare [6,6,3,2,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1332 sg2626

lemma sg12606 : RowSquare [7,5,2,2,1,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1372 sg2702

lemma sg12607 : RowSquare [7,5,2,2,1,1,1,1,1,1,1,1,1] [4,4,4,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1378 sg2702

lemma sg12608 : RowSquare [7,5,2,2,1,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1780 sg2251

lemma sg12609 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg4160

lemma sg12610 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1682 sg2251

lemma sg12611 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg4161

lemma sg12612 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg588 sg4160

lemma sg12613 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg589 sg4160

lemma sg12614 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg590 sg4160

lemma sg12615 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1687 sg2251

lemma sg12616 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg4165

lemma sg12617 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg591 sg4160

lemma sg12618 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg594 sg4160

lemma sg12619 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg587 sg4167

lemma sg12620 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg595 sg4160

lemma sg12621 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [4,4,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg596 sg4160

lemma sg12622 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg588 sg4165

lemma sg12623 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg588 sg4167

lemma sg12624 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg589 sg4167

lemma sg12625 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg597 sg4160

lemma sg12626 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [5,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg599 sg4160

lemma sg12627 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg587 sg4168

lemma sg12628 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [5,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg601 sg4160

lemma sg12629 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [5,4,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg596 sg4161

lemma sg12630 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [5,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg602 sg4160

lemma sg12631 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [6,4,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg601 sg4161

lemma sg12632 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [6,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg607 sg4160

lemma sg12633 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [6,5,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg602 sg4161

lemma sg12634 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [7,5,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg607 sg4161

lemma sg12635 : RowSquare [7,6,2,1,1,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg2702

lemma sg12636 : RowSquare [7,6,2,1,1,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1754 sg2251

lemma sg12637 : RowSquare [7,6,2,1,1,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg2702

lemma sg12638 : RowSquare [7,6,2,1,1,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1755 sg2251

lemma sg12639 : RowSquare [7,6,2,1,1,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg2702

lemma sg12640 : RowSquare [7,6,2,1,1,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1756 sg2251

lemma sg12641 : RowSquare [7,6,2,1,1,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg2254

lemma sg12642 : RowSquare [7,6,2,1,1,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1327 sg2705

lemma sg12643 : RowSquare [7,6,2,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg2255

lemma sg12644 : RowSquare [7,6,2,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1332 sg2702

lemma sg12645 : RowSquare [7,6,2,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1758 sg2251

lemma sg12646 : RowSquare [7,6,2,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg2256

lemma sg12647 : RowSquare [7,6,2,1,1,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1766 sg2251

lemma sg12648 : RowSquare [7,6,2,2,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1257 sg2702

lemma sg12649 : RowSquare [7,6,4,3,2,2,1] [2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1728 sg2019

lemma sg12650 : RowSquare [7,6,4,3,2,2,1] [2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1728 sg2018

lemma sg12651 : RowSquare [7,6,4,3,2,2,1] [2,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1728 sg2017

lemma sg12652 : RowSquare [7,6,4,3,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1728 sg2016

lemma sg12653 : RowSquare [7,6,4,3,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1728 sg2015

lemma sg12654 : RowSquare [7,7,2,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1247 sg2702

lemma sg12655 : RowSquare [7,7,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1248 sg2702

lemma sg12656 : RowSquare [7,7,2,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1249 sg2702

lemma sg12657 : RowSquare [7,7,2,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1250 sg2702

lemma sg12658 : RowSquare [7,7,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1251 sg2702

lemma sg12659 : RowSquare [7,7,2,2,2,2,2,1] [6,4,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11816

lemma sg12660 : RowSquare [7,7,2,2,2,2,2,1] [6,4,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11817

lemma sg12661 : RowSquare [7,7,2,2,2,2,2,1] [6,4,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11818

lemma sg12662 : RowSquare [7,7,2,2,2,2,2,1] [6,4,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg11819

lemma sg12663 : RowSquare [7,7,2,2,2,2,2,1] [6,4,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11820

lemma sg12664 : RowSquare [7,7,2,2,2,2,2,1] [6,4,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11821

lemma sg12665 : RowSquare [7,7,2,2,2,2,2,1] [6,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11822

lemma sg12666 : RowSquare [7,7,2,2,2,2,2,1] [6,4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg11823

lemma sg12667 : RowSquare [7,7,2,2,2,2,2,1] [6,4,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11824

lemma sg12668 : RowSquare [7,7,2,2,2,2,2,1] [6,4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11825

lemma sg12669 : RowSquare [7,7,3,2,2,2,2] [2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1611 sg2104

lemma sg12670 : RowSquare [7,7,3,2,2,2,2] [2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1611 sg2103

lemma sg12671 : RowSquare [7,7,3,2,2,2,2] [2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1611 sg2102

lemma sg12672 : RowSquare [7,7,3,2,2,2,2] [2,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1611 sg2101

lemma sg12673 : RowSquare [7,7,3,2,2,2,2] [2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1611 sg2099

lemma sg12674 : RowSquare [7,7,3,2,2,2,2] [2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1611 sg2097

lemma sg12675 : RowSquare [7,7,3,2,2,2,2] [3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1613 sg2105

lemma sg12676 : RowSquare [7,7,3,2,2,2,2] [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1609 sg2104

lemma sg12677 : RowSquare [7,7,3,2,2,2,2] [3,3,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1609 sg2102

lemma sg12678 : RowSquare [7,7,3,2,2,2,2] [4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1610 sg2105

lemma sg12679 : RowSquare [8,6,1,1,1,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg888 sg3522

lemma sg12680 : RowSquare [8,6,2,1,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg807 sg3521

lemma sg12681 : RowSquare [8,6,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg809 sg3521

lemma sg12682 : RowSquare [8,6,2,1,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg517 sg4345

lemma sg12683 : RowSquare [8,6,2,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg519 sg4345

lemma sg12684 : RowSquare [8,6,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg520 sg4345

lemma sg12685 : RowSquare [8,6,2,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg814 sg3521

lemma sg12686 : RowSquare [8,6,2,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg815 sg3521

lemma sg12687 : RowSquare [8,6,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg816 sg3521

lemma sg12688 : RowSquare [8,6,2,1,1,1,1,1,1,1,1,1] [4,4,4,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg817 sg3521

lemma sg12689 : RowSquare [8,6,2,1,1,1,1,1,1,1,1,1] [5,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg523 sg4345

lemma sg12690 : RowSquare [8,6,2,1,1,1,1,1,1,1,1,1] [5,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg525 sg4345

lemma sg12691 : RowSquare [8,6,2,1,1,1,1,1,1,1,1,1] [5,4,4,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg821 sg3521

lemma sg12692 : RowSquare [8,6,2,1,1,1,1,1,1,1,1,1] [5,5,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg822 sg3521

lemma sg12693 : RowSquare [8,6,2,1,1,1,1,1,1,1,1,1] [5,5,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg823 sg3521

lemma sg12694 : RowSquare [8,6,2,1,1,1,1,1,1,1,1,1] [6,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg528 sg4345

lemma sg12695 : RowSquare [8,6,2,1,1,1,1,1,1,1,1,1] [6,6,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg825 sg3521

lemma sg12696 : RowSquare [8,6,2,2,1,1,1,1,1,1,1] [4,4,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg767 sg3521

lemma sg12697 : RowSquare [8,6,3,2,1,1,1,1,1,1] [6,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg110 sg5735

lemma sg12698 : RowSquare [8,6,3,2,1,1,1,1,1,1] [6,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg111 sg5735

lemma sg12699 : RowSquare [8,6,3,2,1,1,1,1,1,1] [7,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg112 sg5735

lemma sg12700 : RowSquare [8,6,3,2,1,1,1,1,1,1] [8,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg113 sg5735

lemma sg12701 : RowSquare [8,7,2,1,1,1,1,1,1,1,1] [5,5,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg740 sg3521

lemma sg12702 : RowSquare [9,7,2,1,1,1,1,1,1,1] [8,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg109 sg5757

lemma sg12703 : RowSquare [10,3,2,2,2,2,2,1,1] [5,5,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg356 sg4746

lemma sg12704 : RowSquare [10,3,2,2,2,2,2,1,1] [5,5,4,4,4,3] := by
  exact rowSquare_join (by decide) sg74 sg6403

lemma sg12705 : RowSquare [10,3,2,2,2,2,2,1,1] [5,5,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg6404

lemma sg12706 : RowSquare [10,3,2,2,2,2,2,1,1] [5,5,5,4,3,3] := by
  exact rowSquare_join (by decide) sg74 sg6405

lemma sg12707 : RowSquare [10,3,2,2,2,2,2,1,1] [5,5,5,5,5] := by
  exact rowSquare_join (by decide) sg32 sg7807

lemma sg12708 : RowSquare [10,3,2,2,2,2,2,1,1] [6,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg165 sg5620

lemma sg12709 : RowSquare [10,3,2,2,2,2,2,1,1] [6,6,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg356 sg4749

lemma sg12710 : RowSquare [10,3,2,2,2,2,2,2] [6,5,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg165 sg5538

lemma sg12711 : RowSquare [10,3,2,2,2,2,2,2] [6,5,4,4,3,3] := by
  exact rowSquare_join (by decide) sg165 sg5544

lemma sg12712 : RowSquare [10,3,2,2,2,2,2,2] [6,5,4,4,4,2] := by
  exact rowSquare_join (by decide) sg165 sg5545

lemma sg12713 : RowSquare [10,3,2,2,2,2,2,2] [6,5,5,3,3,3] := by
  exact rowSquare_join (by decide) sg165 sg5547

lemma sg12714 : RowSquare [10,3,2,2,2,2,2,2] [6,6,4,3,3,3] := by
  exact rowSquare_join (by decide) sg579 sg3870

lemma sg12715 : RowSquare [10,3,2,2,2,2,2,2] [6,6,5,3,3,2] := by
  exact rowSquare_join (by decide) sg579 sg3871

lemma sg12716 : RowSquare [10,3,2,2,2,2,2,2] [7,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg165 sg5559

lemma sg12717 : RowSquare [10,3,2,2,2,2,2,2] [7,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg165 sg5560

lemma sg12718 : RowSquare [10,3,2,2,2,2,2,2] [7,6,3,3,3,3] := by
  exact rowSquare_join (by decide) sg581 sg3870

lemma sg12719 : RowSquare [10,3,3,2,2,2,2,1] [5,5,5,4,3,3] := by
  exact rowSquare_join (by decide) sg74 sg6293

lemma sg12720 : RowSquare [11,3,2,2,2,2,2,1] [5,5,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg6197

lemma sg12721 : RowSquare [11,3,2,2,2,2,2,1] [5,5,5,4,3,3] := by
  exact rowSquare_join (by decide) sg74 sg6199

lemma sg12722 : RowSquare [12,3,2,2,2,2,2] [6,6,5,4,4] := by
  exact rowSquare_join (by decide) sg27 sg6919

lemma sg12723 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,1] := by
  exact rowSquare_join (by decide) sg1455 sg3732

lemma sg12724 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1456 sg3732

lemma sg12725 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,2] := by
  exact rowSquare_join (by decide) sg1914 sg3068

lemma sg12726 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,1] := by
  exact rowSquare_join (by decide) sg1914 sg3069

lemma sg12727 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,5] := by
  exact rowSquare_join (by decide) sg1532 sg3658

lemma sg12728 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,2] := by
  exact rowSquare_join (by decide) sg1455 sg3733

lemma sg12729 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1533 sg3656

lemma sg12730 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,3,2] := by
  exact rowSquare_join (by decide) sg1915 sg3068

lemma sg12731 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,1] := by
  exact rowSquare_join (by decide) sg2329 sg2432

lemma sg12732 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,3,1] := by
  exact rowSquare_join (by decide) sg2329 sg2433

lemma sg12733 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,4] := by
  exact rowSquare_join (by decide) sg1916 sg3069

lemma sg12734 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,3] := by
  exact rowSquare_join (by decide) sg2432 sg2330

lemma sg12735 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,2] := by
  exact rowSquare_join (by decide) sg2433 sg2330

lemma sg12736 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1970 sg2837

lemma sg12737 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,3,3,3] := by
  exact rowSquare_join (by decide) sg1535 sg3657

lemma sg12738 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1919 sg3069

lemma sg12739 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,4] := by
  exact rowSquare_join (by decide) sg1970 sg2841

lemma sg12740 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,4,3,3,3] := by
  exact rowSquare_join (by decide) sg1536 sg3657

lemma sg12741 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1971 sg2837

lemma sg12742 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1456 sg3734

lemma sg12743 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1972 sg2837

lemma sg12744 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1456 sg3735

lemma sg12745 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,2,2] := by
  exact rowSquare_join (by decide) sg1915 sg3071

lemma sg12746 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,4] := by
  exact rowSquare_join (by decide) sg2432 sg2331

lemma sg12747 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,3] := by
  exact rowSquare_join (by decide) sg2436 sg2330

lemma sg12748 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1063 sg4509

lemma sg12749 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg975 sg4540

lemma sg12750 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1537 sg3656

lemma sg12751 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1973 sg2837

lemma sg12752 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1915 sg3074

lemma sg12753 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,4] := by
  exact rowSquare_join (by decide) sg1916 sg3075

lemma sg12754 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg975 sg4541

lemma sg12755 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1974 sg2837

lemma sg12756 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,3,2,2] := by
  exact rowSquare_join (by decide) sg1915 sg3076

lemma sg12757 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg975 sg4542

lemma sg12758 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,3] := by
  exact rowSquare_join (by decide) sg2432 sg2334

lemma sg12759 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,1,1] := by
  exact rowSquare_join (by decide) sg1915 sg3078

lemma sg12760 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,2] := by
  exact rowSquare_join (by decide) sg2433 sg2334

lemma sg12761 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,3] := by
  exact rowSquare_join (by decide) sg2461 sg2219

lemma sg12762 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,3] := by
  exact rowSquare_join (by decide) sg2432 sg2336

lemma sg12763 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,2] := by
  exact rowSquare_join (by decide) sg2436 sg2332

lemma sg12764 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,3] := by
  exact rowSquare_join (by decide) sg2436 sg2334

lemma sg12765 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2310 sg2432

lemma sg12766 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg2311 sg2432

lemma sg12767 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2310 sg2433

lemma sg12768 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg2311 sg2433

lemma sg12769 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg1891 sg3103

lemma sg12770 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,4,2] := by
  exact rowSquare_join (by decide) sg1455 sg3725

lemma sg12771 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,1] := by
  exact rowSquare_join (by decide) sg1455 sg3726

lemma sg12772 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg2311 sg2434

lemma sg12773 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg2311 sg2435

lemma sg12774 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg2311 sg2436

lemma sg12775 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,4,4,4,3] := by
  exact rowSquare_join (by decide) sg2339 sg2392

lemma sg12776 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2390 sg2341

lemma sg12777 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2311 sg2437

lemma sg12778 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1456 sg3724

lemma sg12779 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2390 sg2343

lemma sg12780 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg2311 sg2439

lemma sg12781 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg2390 sg2344

lemma sg12782 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1891 sg3104

lemma sg12783 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2311 sg2440

lemma sg12784 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg2311 sg2441

lemma sg12785 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,4,4,3,3] := by
  exact rowSquare_join (by decide) sg1844 sg3125

lemma sg12786 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1891 sg3105

lemma sg12787 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,2] := by
  exact rowSquare_join (by decide) sg2340 sg2392

lemma sg12788 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2391 sg2341

lemma sg12789 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg2391 sg2343

lemma sg12790 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg2391 sg2344

lemma sg12791 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2311 sg2444

lemma sg12792 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg2311 sg2445

lemma sg12793 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg2311 sg2446

lemma sg12794 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2390 sg2347

lemma sg12795 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1458 sg3724

lemma sg12796 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2390 sg2348

lemma sg12797 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2390 sg2350

lemma sg12798 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2311 sg2448

lemma sg12799 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2391 sg2347

lemma sg12800 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg2391 sg2351

lemma sg12801 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2311 sg2450

lemma sg12802 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2213 sg2456

lemma sg12803 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2213 sg2457

lemma sg12804 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2214 sg2456

lemma sg12805 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2326 sg2433

lemma sg12806 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1459 sg3724

lemma sg12807 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2213 sg2458

lemma sg12808 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2216 sg2457

lemma sg12809 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2214 sg2458

lemma sg12810 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg2462

lemma sg12811 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2391 sg2353

lemma sg12812 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1803 sg3152

lemma sg12813 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2213 sg2459

lemma sg12814 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2213 sg2460

lemma sg12815 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2391 sg2355

lemma sg12816 : RowSquare [4,4,2,2,2,2,2,2,2,2,1,1] [5,5,5,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1650 sg3106

lemma sg12817 : RowSquare [4,4,3,2,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2311 sg2405

lemma sg12818 : RowSquare [4,4,3,2,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg1926 sg2925

lemma sg12819 : RowSquare [4,4,3,2,2,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg2311 sg2409

lemma sg12820 : RowSquare [4,4,3,2,2,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1927 sg2925

lemma sg12821 : RowSquare [4,4,3,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2311 sg2417

lemma sg12822 : RowSquare [4,4,3,3,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg1891 sg3009

lemma sg12823 : RowSquare [4,4,3,3,2,1,1,1,1,1,1,1,1,1,1] [6,4,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1919 sg2925

lemma sg12824 : RowSquare [4,4,3,3,2,1,1,1,1,1,1,1,1,1,1] [6,5,4,4,4,3] := by
  exact rowSquare_join (by decide) sg2314 sg2392

lemma sg12825 : RowSquare [4,4,3,3,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,4,3,3] := by
  exact rowSquare_join (by decide) sg1032 sg4504

lemma sg12826 : RowSquare [4,4,3,3,2,1,1,1,1,1,1,1,1,1,1] [6,6,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2311 sg2399

lemma sg12827 : RowSquare [4,4,3,3,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,3,3] := by
  exact rowSquare_join (by decide) sg976 sg4521

lemma sg12828 : RowSquare [4,4,3,3,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,2] := by
  exact rowSquare_join (by decide) sg2392 sg2317

lemma sg12829 : RowSquare [4,4,3,3,2,1,1,1,1,1,1,1,1,1,1] [7,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1922 sg2925

lemma sg12830 : RowSquare [4,4,3,3,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg2314 sg2396

lemma sg12831 : RowSquare [4,4,3,3,2,1,1,1,1,1,1,1,1,1,1] [8,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1923 sg2925

lemma sg12832 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1] [6,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg2314 sg2314

lemma sg12833 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [4,4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1033 sg4341

lemma sg12834 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [5,3,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1300 sg3632

lemma sg12835 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [5,4,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1033 sg4342

lemma sg12836 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [5,4,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg2212 sg2284

lemma sg12837 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [6,3,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1300 sg3633

lemma sg12838 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [6,3,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1737 sg2925

lemma sg12839 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [6,3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1301 sg3632

lemma sg12840 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [6,4,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2169 sg2310

lemma sg12841 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [6,4,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2169 sg2311

lemma sg12842 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [6,4,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1738 sg2925

lemma sg12843 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [6,4,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1739 sg2925

lemma sg12844 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [6,4,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1289 sg3648

lemma sg12845 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [6,4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg2214 sg2284

lemma sg12846 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [6,4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg2311 sg2170

lemma sg12847 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [6,5,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1699 sg3004

lemma sg12848 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [6,5,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1740 sg2925

lemma sg12849 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [6,5,4,4,4,3] := by
  exact rowSquare_join (by decide) sg2314 sg2168

lemma sg12850 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [6,6,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1233 sg3730

lemma sg12851 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [6,6,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2311 sg2171

lemma sg12852 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [7,3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2172 sg2310

lemma sg12853 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [7,3,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2172 sg2311

lemma sg12854 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [7,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1741 sg2925

lemma sg12855 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [7,4,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2169 sg2314

lemma sg12856 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [7,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1742 sg2925

lemma sg12857 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [7,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg2215 sg2286

lemma sg12858 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [8,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2221 sg2284

lemma sg12859 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [8,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2172 sg2314

lemma sg12860 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [8,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1743 sg2925

lemma sg12861 : RowSquare [5,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2407

lemma sg12862 : RowSquare [5,4,3,2,2,2,2,2,2,1,1] [7,6,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1493 sg3299

lemma sg12863 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1] [5,4,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg2311 sg2167

lemma sg12864 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1] [5,5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1688 sg3004

lemma sg12865 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1] [6,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg2314 sg2167

lemma sg12866 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,4,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2288 sg2375

lemma sg12867 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2369 sg2289

lemma sg12868 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2369 sg2291

lemma sg12869 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2290 sg2371

lemma sg12870 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2379

lemma sg12871 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2380

lemma sg12872 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2381

lemma sg12873 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2290 sg2373

lemma sg12874 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2290 sg2374

lemma sg12875 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2370 sg2291

lemma sg12876 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2382

lemma sg12877 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2371 sg2292

lemma sg12878 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2383

lemma sg12879 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2371 sg2293

lemma sg12880 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2370 sg2296

lemma sg12881 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2384

lemma sg12882 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2385

lemma sg12883 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2386

lemma sg12884 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2371 sg2297

lemma sg12885 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg2293 sg2373

lemma sg12886 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg2293 sg2374

lemma sg12887 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,5,2,1] := by
  exact rowSquare_join (by decide) sg2373 sg2297

lemma sg12888 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,5,3] := by
  exact rowSquare_join (by decide) sg2374 sg2297

lemma sg12889 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2369 sg2298

lemma sg12890 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2290 sg2376

lemma sg12891 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2370 sg2298

lemma sg12892 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2387

lemma sg12893 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2290 sg2381

lemma sg12894 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2370 sg2301

lemma sg12895 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2370 sg2302

lemma sg12896 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2290 sg2384

lemma sg12897 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg2293 sg2381

lemma sg12898 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,5,2,1] := by
  exact rowSquare_join (by decide) sg2379 sg2297

lemma sg12899 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,5,3] := by
  exact rowSquare_join (by decide) sg2380 sg2297

lemma sg12900 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2370 sg2305

lemma sg12901 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2370 sg2306

lemma sg12902 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2388

lemma sg12903 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1779 sg3115

lemma sg12904 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2293 sg2382

lemma sg12905 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2389

lemma sg12906 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2371 sg2307

lemma sg12907 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1782 sg3115

lemma sg12908 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg2293 sg2384

lemma sg12909 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2370 sg2309

lemma sg12910 : RowSquare [5,5,2,2,2,2,2,2,2,1,1] [7,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1086 sg3998

lemma sg12911 : RowSquare [5,5,2,2,2,2,2,2,2,1,1] [7,5,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1082 sg3999

lemma sg12912 : RowSquare [5,5,2,2,2,2,2,2,2,1,1] [8,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1084 sg3999

lemma sg12913 : RowSquare [5,5,2,2,2,2,2,2,2,1,1] [8,5,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1086 sg3999

lemma sg12914 : RowSquare [5,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,6,6,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg4496

lemma sg12915 : RowSquare [5,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,6,6,2] := by
  exact rowSquare_join (by decide) sg1001 sg4496

lemma sg12916 : RowSquare [5,5,3,3,2,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1682 sg2902

lemma sg12917 : RowSquare [5,5,3,3,2,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg586 sg4918

lemma sg12918 : RowSquare [5,5,3,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg586 sg4922

lemma sg12919 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1] [5,5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1688 sg2746

lemma sg12920 : RowSquare [6,5,3,2,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg2746

lemma sg12921 : RowSquare [7,6,2,2,1,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg2702

lemma sg12922 : RowSquare [7,6,2,2,1,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1756 sg2702

lemma sg12923 : RowSquare [7,6,2,2,1,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1754 sg2705

lemma sg12924 : RowSquare [7,6,2,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1757 sg2702

lemma sg12925 : RowSquare [7,6,2,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg2706

lemma sg12926 : RowSquare [7,6,2,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg2707

lemma sg12927 : RowSquare [7,6,2,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg2708

lemma sg12928 : RowSquare [7,6,2,2,1,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1759 sg2702

lemma sg12929 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg888 sg4160

lemma sg12930 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2251 sg2134

lemma sg12931 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg892 sg4165

lemma sg12932 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg892 sg4167

lemma sg12933 : RowSquare [7,7,2,1,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1748 sg2702

lemma sg12934 : RowSquare [7,7,2,1,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2251 sg2156

lemma sg12935 : RowSquare [8,6,2,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg891 sg4348

lemma sg12936 : RowSquare [8,6,2,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg892 sg4348

lemma sg12937 : RowSquare [8,6,2,2,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg807 sg4345

lemma sg12938 : RowSquare [8,6,2,2,1,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg809 sg4345

lemma sg12939 : RowSquare [8,6,2,2,1,1,1,1,1,1,1,1] [4,4,4,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg817 sg4345

end UniversalTensorSquare
end
end

end OAI
