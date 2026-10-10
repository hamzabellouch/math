import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes17
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes20

namespace OAI

/-! Semigroup Nodes 25. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10538 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [10,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg7018

lemma sg10539 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [10,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg7019

lemma sg10540 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [10,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg5182

lemma sg10541 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [10,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg7020

lemma sg10542 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [10,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg5165

lemma sg10543 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [10,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg15 sg5140

lemma sg10544 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [10,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5183

lemma sg10545 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [10,4,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg5184

lemma sg10546 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [10,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5185

lemma sg10547 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [10,4,4,2,2] := by
  exact rowSquare_join (by decide) sg83 sg3745

lemma sg10548 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [10,4,4,3,1] := by
  exact rowSquare_join (by decide) sg13 sg5186

lemma sg10549 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [10,4,4,4] := by
  exact rowSquare_join (by decide) sg13 sg5187

lemma sg10550 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [10,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg14 sg5166

lemma sg10551 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [10,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5188

lemma sg10552 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [10,5,4,3] := by
  exact rowSquare_join (by decide) sg13 sg5189

lemma sg10553 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [10,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg7021

lemma sg10554 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [10,6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5190

lemma sg10555 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [10,6,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg5171

lemma sg10556 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [10,6,3,3] := by
  exact rowSquare_join (by decide) sg13 sg5191

lemma sg10557 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [10,6,4,2] := by
  exact rowSquare_join (by decide) sg83 sg3748

lemma sg10558 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [10,8,2,2] := by
  exact rowSquare_join (by decide) sg13 sg5192

lemma sg10559 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [11,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg7022

lemma sg10560 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [11,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg15 sg5147

lemma sg10561 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [11,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg7023

lemma sg10562 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [11,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg15 sg5149

lemma sg10563 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [11,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5193

lemma sg10564 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [11,3,3,3,2] := by
  exact rowSquare_join (by decide) sg84 sg3745

lemma sg10565 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [11,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg14 sg5182

lemma sg10566 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [11,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5194

lemma sg10567 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [11,4,3,2,2] := by
  exact rowSquare_join (by decide) sg15 sg5155

lemma sg10568 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [11,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg3750

lemma sg10569 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [11,4,4,3] := by
  exact rowSquare_join (by decide) sg13 sg5195

lemma sg10570 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [11,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg7024

lemma sg10571 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [11,5,3,3] := by
  exact rowSquare_join (by decide) sg84 sg3748

lemma sg10572 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [11,7,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5190

lemma sg10573 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [12,4,3,3] := by
  exact rowSquare_join (by decide) sg84 sg3751

lemma sg10574 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [12,4,4,2] := by
  exact rowSquare_join (by decide) sg364 sg2485

lemma sg10575 : RowSquare [6,6,2,1,1,1,1,1,1,1,1] [5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5208

lemma sg10576 : RowSquare [6,6,2,1,1,1,1,1,1,1,1] [6,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg905 sg1754

lemma sg10577 : RowSquare [6,6,2,1,1,1,1,1,1,1,1] [6,4,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg906 sg1754

lemma sg10578 : RowSquare [6,6,2,1,1,1,1,1,1,1,1] [6,4,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg907 sg1754

lemma sg10579 : RowSquare [6,6,2,1,1,1,1,1,1,1,1] [6,5,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg908 sg1754

lemma sg10580 : RowSquare [6,6,2,1,1,1,1,1,1,1,1] [6,6,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg909 sg1754

lemma sg10581 : RowSquare [6,6,2,2,2,2,1,1] [4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg7813

lemma sg10582 : RowSquare [6,6,2,2,2,2,1,1] [4,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg7816

lemma sg10583 : RowSquare [6,6,2,2,2,2,1,1] [4,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg7817

lemma sg10584 : RowSquare [6,6,2,2,2,2,1,1] [4,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg7818

lemma sg10585 : RowSquare [6,6,2,2,2,2,1,1] [4,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg7819

lemma sg10586 : RowSquare [6,6,2,2,2,2,1,1] [4,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg7820

lemma sg10587 : RowSquare [6,6,2,2,2,2,1,1] [4,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg7821

lemma sg10588 : RowSquare [6,6,2,2,2,2,1,1] [5,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg7824

lemma sg10589 : RowSquare [6,6,2,2,2,2,1,1] [5,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg7825

lemma sg10590 : RowSquare [6,6,2,2,2,2,1,1] [5,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg7826

lemma sg10591 : RowSquare [6,6,2,2,2,2,1,1] [5,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg7827

lemma sg10592 : RowSquare [6,6,2,2,2,2,1,1] [5,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg7828

lemma sg10593 : RowSquare [6,6,2,2,2,2,1,1] [5,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg7837

lemma sg10594 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg2251

lemma sg10595 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg2251

lemma sg10596 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg2252

lemma sg10597 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg588 sg2251

lemma sg10598 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg589 sg2251

lemma sg10599 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg590 sg2251

lemma sg10600 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg594 sg2251

lemma sg10601 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg587 sg2256

lemma sg10602 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg595 sg2251

lemma sg10603 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [4,4,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg596 sg2251

lemma sg10604 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg589 sg2253

lemma sg10605 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg588 sg2254

lemma sg10606 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg589 sg2254

lemma sg10607 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [4,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg590 sg2254

lemma sg10608 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg589 sg2255

lemma sg10609 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg589 sg2256

lemma sg10610 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg590 sg2255

lemma sg10611 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg597 sg2251

lemma sg10612 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg591 sg2252

lemma sg10613 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg592 sg2252

lemma sg10614 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8539

lemma sg10615 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg587 sg2259

lemma sg10616 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8541

lemma sg10617 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg587 sg2260

lemma sg10618 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg600 sg2251

lemma sg10619 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg588 sg2257

lemma sg10620 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg601 sg2251

lemma sg10621 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg589 sg2257

lemma sg10622 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8546

lemma sg10623 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8549

lemma sg10624 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8550

lemma sg10625 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg588 sg2260

lemma sg10626 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg593 sg2254

lemma sg10627 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg589 sg2258

lemma sg10628 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8551

lemma sg10629 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg594 sg2254

lemma sg10630 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg590 sg2258

lemma sg10631 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8552

lemma sg10632 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8553

lemma sg10633 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8554

lemma sg10634 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8555

lemma sg10635 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg594 sg2255

lemma sg10636 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg590 sg2259

lemma sg10637 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8556

lemma sg10638 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8557

lemma sg10639 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg0 sg8558

lemma sg10640 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg0 sg8559

lemma sg10641 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,5,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg602 sg2251

lemma sg10642 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg2267

lemma sg10643 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg595 sg2254

lemma sg10644 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg588 sg2262

lemma sg10645 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,5,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg590 sg2261

lemma sg10646 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg588 sg2263

lemma sg10647 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg595 sg2256

lemma sg10648 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,5,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg596 sg2254

lemma sg10649 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg589 sg2262

lemma sg10650 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,5,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg596 sg2255

lemma sg10651 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg590 sg2262

lemma sg10652 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg589 sg2263

lemma sg10653 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg590 sg2263

lemma sg10654 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg603 sg2251

lemma sg10655 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg597 sg2252

lemma sg10656 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg605 sg2251

lemma sg10657 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8567

lemma sg10658 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8569

lemma sg10659 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8570

lemma sg10660 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg591 sg2260

lemma sg10661 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,4,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg606 sg2251

lemma sg10662 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg6910

lemma sg10663 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg6030

lemma sg10664 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg6912

lemma sg10665 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8574

lemma sg10666 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg6913

lemma sg10667 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8575

lemma sg10668 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg599 sg2254

lemma sg10669 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6031

lemma sg10670 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8576

lemma sg10671 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg6032

lemma sg10672 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6033

lemma sg10673 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8577

lemma sg10674 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg6034

lemma sg10675 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6035

lemma sg10676 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg0 sg8578

lemma sg10677 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg594 sg2259

lemma sg10678 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8579

lemma sg10679 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg2 sg6917

lemma sg10680 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg2 sg6918

lemma sg10681 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,4,4,4,4] := by
  exact rowSquare_join (by decide) sg2 sg6919

lemma sg10682 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,5,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg607 sg2251

lemma sg10683 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8585

lemma sg10684 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6036

lemma sg10685 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8589

lemma sg10686 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8591

lemma sg10687 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8592

lemma sg10688 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8593

lemma sg10689 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg0 sg8594

lemma sg10690 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg601 sg2254

lemma sg10691 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,5,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg596 sg2258

lemma sg10692 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6037

lemma sg10693 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg6038

lemma sg10694 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6039

lemma sg10695 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6040

lemma sg10696 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6041

lemma sg10697 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg4 sg6042

lemma sg10698 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,5,5,3,3] := by
  exact rowSquare_join (by decide) sg4 sg6043

lemma sg10699 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6044

lemma sg10700 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,5,5,4,2] := by
  exact rowSquare_join (by decide) sg4 sg6045

lemma sg10701 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,6,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg2269

lemma sg10702 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg602 sg2254

lemma sg10703 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg608 sg2251

lemma sg10704 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg609 sg2251

lemma sg10705 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg610 sg2251

lemma sg10706 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg605 sg2254

lemma sg10707 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5304

lemma sg10708 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6051

lemma sg10709 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5307

lemma sg10710 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,5,4,4,2] := by
  exact rowSquare_join (by decide) sg13 sg5308

lemma sg10711 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5309

lemma sg10712 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg6052

lemma sg10713 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5310

lemma sg10714 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,5,5,3,2] := by
  exact rowSquare_join (by decide) sg13 sg5311

lemma sg10715 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,5,5,4,1] := by
  exact rowSquare_join (by decide) sg4 sg6053

lemma sg10716 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6054

lemma sg10717 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,6,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6055

lemma sg10718 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,6,4,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg6056

lemma sg10719 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6057

lemma sg10720 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,6,4,3,2] := by
  exact rowSquare_join (by decide) sg4 sg6058

lemma sg10721 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,6,4,4,1] := by
  exact rowSquare_join (by decide) sg0 sg8606

lemma sg10722 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,6,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6059

lemma sg10723 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,6,5,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6060

lemma sg10724 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,6,5,2,2] := by
  exact rowSquare_join (by decide) sg4 sg6061

lemma sg10725 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,6,5,3,1] := by
  exact rowSquare_join (by decide) sg4 sg6062

lemma sg10726 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,6,5,4] := by
  exact rowSquare_join (by decide) sg4 sg6063

lemma sg10727 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,7,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg602 sg2261

lemma sg10728 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,7,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg588 sg2269

lemma sg10729 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,7,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg602 sg2262

lemma sg10730 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,7,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg596 sg2267

lemma sg10731 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,7,3,2,2,1] := by
  exact rowSquare_join (by decide) sg589 sg2269

lemma sg10732 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,7,3,3,2] := by
  exact rowSquare_join (by decide) sg590 sg2269

lemma sg10733 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,7,4,2,1,1] := by
  exact rowSquare_join (by decide) sg596 sg2268

lemma sg10734 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg611 sg2251

lemma sg10735 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg608 sg2252

lemma sg10736 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg7292

lemma sg10737 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg7293

lemma sg10738 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6 sg6029

lemma sg10739 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg6956

lemma sg10740 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg612 sg2251

lemma sg10741 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg609 sg2252

lemma sg10742 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg7294

lemma sg10743 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg7295

lemma sg10744 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg6046

lemma sg10745 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg6047

lemma sg10746 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg7296

lemma sg10747 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg7297

lemma sg10748 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6064

lemma sg10749 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6065

lemma sg10750 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg16 sg5135

lemma sg10751 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5312

lemma sg10752 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5313

lemma sg10753 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6 sg6034

lemma sg10754 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6 sg6035

lemma sg10755 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1 sg7298

lemma sg10756 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg610 sg2252

lemma sg10757 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg7299

lemma sg10758 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg7300

lemma sg10759 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5302

lemma sg10760 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5 sg6048

lemma sg10761 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg17 sg5135

lemma sg10762 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg7301

lemma sg10763 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5314

lemma sg10764 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6066

lemma sg10765 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg16 sg5136

lemma sg10766 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5315

lemma sg10767 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5316

lemma sg10768 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg5 sg6049

lemma sg10769 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg5 sg6050

lemma sg10770 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6067

lemma sg10771 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5317

lemma sg10772 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg16 sg5137

lemma sg10773 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg6068

lemma sg10774 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5318

lemma sg10775 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg5319

lemma sg10776 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,4,4,3,3] := by
  exact rowSquare_join (by decide) sg4 sg6069

lemma sg10777 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5320

lemma sg10778 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,2] := by
  exact rowSquare_join (by decide) sg13 sg5321

lemma sg10779 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg7302

lemma sg10780 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8607

lemma sg10781 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5322

lemma sg10782 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5303

lemma sg10783 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg17 sg5136

lemma sg10784 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5304

lemma sg10785 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5323

lemma sg10786 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg5137

lemma sg10787 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg16 sg5139

lemma sg10788 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5324

lemma sg10789 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg5325

lemma sg10790 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,5,3,3,3] := by
  exact rowSquare_join (by decide) sg14 sg5305

lemma sg10791 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6070

lemma sg10792 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5326

lemma sg10793 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg16 sg5140

lemma sg10794 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5327

lemma sg10795 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,5,4,3,2] := by
  exact rowSquare_join (by decide) sg13 sg5328

lemma sg10796 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,1] := by
  exact rowSquare_join (by decide) sg13 sg5329

lemma sg10797 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6071

lemma sg10798 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5330

lemma sg10799 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,5,5,2,2] := by
  exact rowSquare_join (by decide) sg16 sg5142

lemma sg10800 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,5,5,3,1] := by
  exact rowSquare_join (by decide) sg13 sg5331

lemma sg10801 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,5,5,4] := by
  exact rowSquare_join (by decide) sg16 sg5144

lemma sg10802 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8608

lemma sg10803 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6072

lemma sg10804 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5332

lemma sg10805 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,6,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8609

lemma sg10806 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg17 sg5139

lemma sg10807 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5306

lemma sg10808 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,6,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5333

lemma sg10809 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,6,3,2,2,1] := by
  exact rowSquare_join (by decide) sg17 sg5140

lemma sg10810 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,6,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5334

lemma sg10811 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,6,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg5335

lemma sg10812 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,6,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5309

lemma sg10813 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,6,4,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5336

lemma sg10814 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,6,4,2,2] := by
  exact rowSquare_join (by decide) sg17 sg5142

lemma sg10815 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,6,4,3,1] := by
  exact rowSquare_join (by decide) sg13 sg5337

lemma sg10816 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,6,4,4] := by
  exact rowSquare_join (by decide) sg13 sg5338

lemma sg10817 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,6,5,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6073

lemma sg10818 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,6,5,2,1] := by
  exact rowSquare_join (by decide) sg13 sg5339

lemma sg10819 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,6,5,3] := by
  exact rowSquare_join (by decide) sg13 sg5340

lemma sg10820 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,7,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8611

lemma sg10821 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,7,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6074

lemma sg10822 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,7,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8612

lemma sg10823 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,7,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8613

lemma sg10824 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,7,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6075

lemma sg10825 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,7,3,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6076

lemma sg10826 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,7,3,2,2] := by
  exact rowSquare_join (by decide) sg4 sg6077

lemma sg10827 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,7,3,3,1] := by
  exact rowSquare_join (by decide) sg0 sg8614

lemma sg10828 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,7,4,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6078

lemma sg10829 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,7,4,2,1] := by
  exact rowSquare_join (by decide) sg4 sg6079

lemma sg10830 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,7,4,3] := by
  exact rowSquare_join (by decide) sg4 sg6080

lemma sg10831 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,8,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg602 sg2267

lemma sg10832 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,8,2,2,2] := by
  exact rowSquare_join (by decide) sg595 sg2269

lemma sg10833 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,8,3,1,1,1] := by
  exact rowSquare_join (by decide) sg602 sg2268

lemma sg10834 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,8,3,2,1] := by
  exact rowSquare_join (by decide) sg596 sg2269

lemma sg10835 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [9,5,4,4] := by
  exact rowSquare_join (by decide) sg39 sg4583

lemma sg10836 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [9,6,4,3] := by
  exact rowSquare_join (by decide) sg40 sg4583

lemma sg10837 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [10,4,4,4] := by
  exact rowSquare_join (by decide) sg39 sg4584

lemma sg10838 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [10,5,4,3] := by
  exact rowSquare_join (by decide) sg39 sg4585

lemma sg10839 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [10,6,3,3] := by
  exact rowSquare_join (by decide) sg39 sg4586

lemma sg10840 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [10,6,4,2] := by
  exact rowSquare_join (by decide) sg97 sg3748

lemma sg10841 : RowSquare [7,5,2,1,1,1,1,1,1,1,1] [4,4,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg543 sg2251

lemma sg10842 : RowSquare [7,5,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg316 sg2708

lemma sg10843 : RowSquare [7,5,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg312 sg2710

lemma sg10844 : RowSquare [7,5,2,2,1,1,1,1,1,1] [3,3,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg270 sg2702

lemma sg10845 : RowSquare [7,5,2,2,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg271 sg2702

lemma sg10846 : RowSquare [7,5,2,2,1,1,1,1,1,1] [4,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg272 sg2702

lemma sg10847 : RowSquare [7,5,2,2,1,1,1,1,1,1] [4,4,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg276 sg2702

lemma sg10848 : RowSquare [7,5,2,2,1,1,1,1,1,1] [4,4,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg496 sg2251

lemma sg10849 : RowSquare [7,5,2,2,1,1,1,1,1,1] [5,5,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg281 sg2702

lemma sg10850 : RowSquare [7,5,2,2,1,1,1,1,1,1] [5,5,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg496 sg2253

lemma sg10851 : RowSquare [7,5,2,2,1,1,1,1,1,1] [7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg7454

lemma sg10852 : RowSquare [7,6,2,1,1,1,1,1,1,1] [4,4,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg457 sg2251

lemma sg10853 : RowSquare [7,6,2,1,1,1,1,1,1,1] [4,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg5417

lemma sg10854 : RowSquare [7,6,2,1,1,1,1,1,1,1] [4,4,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg459 sg2251

lemma sg10855 : RowSquare [7,6,2,1,1,1,1,1,1,1] [4,4,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1191

lemma sg10856 : RowSquare [7,6,2,1,1,1,1,1,1,1] [4,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg5420

lemma sg10857 : RowSquare [7,6,2,1,1,1,1,1,1,1] [4,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5421

lemma sg10858 : RowSquare [7,6,2,1,1,1,1,1,1,1] [4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5422

lemma sg10859 : RowSquare [7,6,2,1,1,1,1,1,1,1] [5,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg74 sg3866

lemma sg10860 : RowSquare [7,6,2,1,1,1,1,1,1,1] [5,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg3867

lemma sg10861 : RowSquare [7,6,2,1,1,1,1,1,1,1] [5,5,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg465 sg2251

lemma sg10862 : RowSquare [7,6,2,1,1,1,1,1,1,1] [5,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg74 sg3870

lemma sg10863 : RowSquare [7,6,2,1,1,1,1,1,1,1] [5,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg459 sg2254

lemma sg10864 : RowSquare [7,6,2,1,1,1,1,1,1,1] [5,5,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5429

lemma sg10865 : RowSquare [7,6,2,1,1,1,1,1,1,1] [5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg74 sg3875

lemma sg10866 : RowSquare [7,6,2,1,1,1,1,1,1,1] [6,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg3876

lemma sg10868 : RowSquare [7,6,2,2,2,2,1] [2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1222 sg1177

lemma sg10869 : RowSquare [7,6,2,2,2,2,1] [2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1219 sg1177

lemma sg10870 : RowSquare [7,6,2,2,2,2,1] [2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1219 sg1176

lemma sg10871 : RowSquare [7,6,2,2,2,2,1] [2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1219 sg1174

lemma sg10872 : RowSquare [7,6,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1219 sg1172

lemma sg10873 : RowSquare [7,6,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1219 sg1169

lemma sg10874 : RowSquare [7,6,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg780 sg1644

lemma sg10875 : RowSquare [7,6,2,2,2,2,1] [3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1218 sg1177

lemma sg10876 : RowSquare [7,6,2,2,2,2,1] [3,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1218 sg1176

lemma sg10877 : RowSquare [7,6,2,2,2,2,1] [3,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1218 sg1175

lemma sg10878 : RowSquare [7,6,2,2,2,2,1] [3,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1218 sg1174

lemma sg10879 : RowSquare [7,6,2,2,2,2,1] [3,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1218 sg1172

lemma sg10880 : RowSquare [7,6,2,2,2,2,1] [3,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1218 sg1169

lemma sg10881 : RowSquare [7,6,2,2,2,2,1] [3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1220 sg1177

lemma sg10882 : RowSquare [7,6,2,2,2,2,1] [3,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1217 sg1170

lemma sg10883 : RowSquare [7,6,2,2,2,2,1] [3,3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1215 sg1170

lemma sg10884 : RowSquare [7,6,2,2,2,2,1] [3,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1215 sg1167

lemma sg10885 : RowSquare [7,6,2,2,2,2,1] [3,3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1215 sg1163

lemma sg10886 : RowSquare [7,6,2,2,2,2,1] [3,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1217 sg1162

lemma sg10887 : RowSquare [7,6,2,2,2,2,1] [3,3,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1215 sg1162

lemma sg10888 : RowSquare [7,6,2,2,2,2,1] [3,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1215 sg1157

lemma sg10889 : RowSquare [7,6,2,2,2,2,1] [4,3,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1214 sg1177

lemma sg10890 : RowSquare [7,6,2,2,2,2,1] [4,3,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1214 sg1176

lemma sg10891 : RowSquare [7,6,2,2,2,2,1] [4,3,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1214 sg1175

lemma sg10892 : RowSquare [7,6,2,2,2,2,1] [4,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1214 sg1174

lemma sg10893 : RowSquare [7,6,2,2,2,2,1] [4,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1214 sg1172

lemma sg10894 : RowSquare [7,6,2,2,2,2,1] [4,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1214 sg1169

lemma sg10895 : RowSquare [7,6,2,2,2,2,1] [4,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1213 sg1173

lemma sg10896 : RowSquare [7,6,2,2,2,2,1] [4,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1213 sg1171

lemma sg10897 : RowSquare [7,6,2,2,2,2,1] [4,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1213 sg1168

lemma sg10898 : RowSquare [7,6,2,2,2,2,1] [4,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1213 sg1164

lemma sg10899 : RowSquare [7,6,2,2,2,2,1] [4,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1213 sg1170

lemma sg10900 : RowSquare [7,6,2,2,2,2,1] [4,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1213 sg1167

lemma sg10901 : RowSquare [7,6,2,2,2,2,1] [4,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1213 sg1163

lemma sg10902 : RowSquare [7,6,2,2,2,2,1] [4,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1214 sg1157

lemma sg10903 : RowSquare [7,6,2,2,2,2,1] [4,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1213 sg1162

lemma sg10904 : RowSquare [7,6,2,2,2,2,1] [4,4,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1212 sg1170

lemma sg10905 : RowSquare [7,6,2,2,2,2,1] [4,4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1212 sg1167

lemma sg10906 : RowSquare [7,6,2,2,2,2,1] [4,4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1212 sg1163

lemma sg10907 : RowSquare [7,6,2,2,2,2,1] [4,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1216 sg1162

lemma sg10908 : RowSquare [7,6,2,2,2,2,1] [4,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1213 sg1154

lemma sg10909 : RowSquare [7,6,2,2,2,2,1] [4,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1212 sg1166

lemma sg10910 : RowSquare [7,6,2,2,2,2,1] [5,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1207 sg1170

lemma sg10911 : RowSquare [7,6,2,2,2,2,1] [7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg6317

lemma sg10912 : RowSquare [7,6,2,2,2,2,1] [7,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg6318

lemma sg10913 : RowSquare [7,6,2,2,2,2,1] [7,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6329

lemma sg10914 : RowSquare [7,6,2,2,2,2,1] [7,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5519

lemma sg10915 : RowSquare [7,6,2,2,2,2,1] [7,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg7801

lemma sg10916 : RowSquare [7,6,2,2,2,2,1] [7,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg7802

lemma sg10917 : RowSquare [7,6,2,2,2,2,1] [7,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg7803

lemma sg10918 : RowSquare [7,6,2,2,2,2,1] [7,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg7804

lemma sg10919 : RowSquare [7,6,2,2,2,2,1] [7,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5515

lemma sg10920 : RowSquare [7,6,2,2,2,2,1] [7,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6330

lemma sg10921 : RowSquare [7,6,2,2,2,2,1] [7,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg4701

lemma sg10922 : RowSquare [7,6,2,2,2,2,1] [7,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg6319

lemma sg10923 : RowSquare [7,6,2,2,2,2,1] [7,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg6320

lemma sg10924 : RowSquare [7,6,2,2,2,2,1] [7,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5 sg6321

lemma sg10925 : RowSquare [7,6,2,2,2,2,1] [7,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg6322

lemma sg10926 : RowSquare [7,6,2,2,2,2,1] [7,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg4699

lemma sg10927 : RowSquare [7,6,2,2,2,2,1] [7,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg4702

lemma sg10928 : RowSquare [7,6,2,2,2,2,1] [7,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6331

lemma sg10929 : RowSquare [7,6,2,2,2,2,1] [7,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6332

lemma sg10930 : RowSquare [7,6,2,2,2,2,1] [7,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg6333

lemma sg10931 : RowSquare [7,6,2,2,2,2,1] [7,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg3859

lemma sg10932 : RowSquare [7,6,2,2,2,2,1] [7,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5520

lemma sg10933 : RowSquare [7,6,2,2,2,2,1] [7,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg84 sg3860

lemma sg10934 : RowSquare [7,6,2,2,2,2,1] [7,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg5521

lemma sg10935 : RowSquare [7,6,2,2,2,2,1] [7,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1209 sg1146

lemma sg10936 : RowSquare [7,6,2,2,2,2,1] [7,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg776 sg1632

lemma sg10937 : RowSquare [7,6,2,2,2,2,1] [7,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg6323

lemma sg10938 : RowSquare [7,6,2,2,2,2,1] [7,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg4701

end UniversalTensorSquare
end
end

end OAI
