import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes51
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes21
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes24
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes44
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes39
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes41

namespace OAI

/-! Semigroup Nodes 60. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24540 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9737

lemma sg24541 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8659 sg9668

lemma sg24542 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg8460 sg10184

lemma sg24543 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8422 sg10237

lemma sg24544 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10237

lemma sg24545 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8658 sg9669

lemma sg24546 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg8350 sg10642

lemma sg24547 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg8659 sg9669

lemma sg24548 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8722 sg9495

lemma sg24549 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10315

lemma sg24550 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9497

lemma sg24551 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8658 sg9670

lemma sg24552 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9738

lemma sg24553 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8347 sg10647

lemma sg24554 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8461 sg10184

lemma sg24555 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8455 sg10189

lemma sg24556 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg7452 sg11275

lemma sg24557 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9739

lemma sg24558 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10238

lemma sg24559 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8665 sg9662

lemma sg24560 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg8457 sg10189

lemma sg24561 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8432 sg10231

lemma sg24562 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8658 sg9671

lemma sg24563 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg8430 sg10232

lemma sg24564 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg8659 sg9671

lemma sg24565 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,4,4,4] := by
  exact rowSquare_join (by decide) sg7806 sg11239

lemma sg24566 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8525 sg10108

lemma sg24567 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5569 sg12616

lemma sg24568 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8542 sg10091

lemma sg24569 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg7239 sg11444

lemma sg24570 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg8352 sg10642

lemma sg24571 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg8543 sg10090

lemma sg24572 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg5538 sg12622

lemma sg24573 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg8543 sg10091

lemma sg24574 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,5,4,3] := by
  exact rowSquare_join (by decide) sg7806 sg11240

lemma sg24575 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg8432 sg10232

lemma sg24576 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg6402 sg11735

lemma sg24577 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,3,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8650 sg9740

lemma sg24578 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,3,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8845 sg9157

lemma sg24579 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg7232 sg11460

lemma sg24580 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,4,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8720 sg9500

lemma sg24581 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,4,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10316

lemma sg24582 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,4,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8464 sg10184

lemma sg24583 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,4,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8347 sg10648

lemma sg24584 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,4,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8736 sg9457

lemma sg24585 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,4,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8720 sg9501

lemma sg24586 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,4,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9741

lemma sg24587 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,4,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8668 sg9662

lemma sg24588 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,4,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8820 sg9162

lemma sg24589 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,4,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10317

lemma sg24590 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9502

lemma sg24591 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,4,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8367 sg10606

lemma sg24592 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,4,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9742

lemma sg24593 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,4,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10239

lemma sg24594 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,4,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg8860 sg9043

lemma sg24595 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,4,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9743

lemma sg24596 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,4,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8658 sg9673

lemma sg24597 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,4,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10235

lemma sg24598 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9044

lemma sg24599 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,4,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg8457 sg10190

lemma sg24600 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8721 sg9500

lemma sg24601 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10318

lemma sg24602 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9744

lemma sg24603 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8670 sg9662

lemma sg24604 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8347 sg10650

lemma sg24605 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8722 sg9500

lemma sg24606 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10319

lemma sg24607 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9504

lemma sg24608 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8367 sg10607

lemma sg24609 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9745

lemma sg24610 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10240

lemma sg24611 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8860 sg9046

lemma sg24612 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9502

lemma sg24613 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8661 sg9668

lemma sg24614 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9746

lemma sg24615 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10241

lemma sg24616 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8661 sg9669

lemma sg24617 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9047

lemma sg24618 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9505

lemma sg24619 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10237

lemma sg24620 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9048

lemma sg24621 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg8350 sg10644

lemma sg24622 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg8662 sg9669

lemma sg24623 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8722 sg9501

lemma sg24624 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8736 sg9461

lemma sg24625 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8661 sg9670

lemma sg24626 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9747

lemma sg24627 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8658 sg9677

lemma sg24628 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8662 sg9670

lemma sg24629 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9049

lemma sg24630 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9748

lemma sg24631 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10242

lemma sg24632 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9507

lemma sg24633 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10238

lemma sg24634 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9050

lemma sg24635 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg8457 sg10192

lemma sg24636 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8658 sg9678

lemma sg24637 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg8659 sg9678

lemma sg24638 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,5,4,4,3] := by
  exact rowSquare_join (by decide) sg8662 sg9671

lemma sg24639 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8526 sg10108

lemma sg24640 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg7239 sg11446

lemma sg24641 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9051

lemma sg24642 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8372 sg10605

lemma sg24643 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg8543 sg10094

lemma sg24644 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,5,5,3,3] := by
  exact rowSquare_join (by decide) sg8546 sg10090

lemma sg24645 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg8864 sg8994

lemma sg24646 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,5,5,4,2] := by
  exact rowSquare_join (by decide) sg8546 sg10091

lemma sg24647 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1868 sg16187

lemma sg24648 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2227 sg15519

lemma sg24649 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2870 sg14850

lemma sg24650 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5577 sg12612

lemma sg24651 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5246 sg12687

lemma sg24652 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8590 sg10081

lemma sg24653 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9203

lemma sg24654 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8739 sg9453

lemma sg24655 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2871 sg14850

lemma sg24656 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5551 sg12620

lemma sg24657 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5247 sg12687

lemma sg24658 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8591 sg10081

lemma sg24659 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9204

lemma sg24660 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9736

lemma sg24661 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8739 sg9454

lemma sg24662 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5248 sg12687

lemma sg24663 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8556 sg10087

lemma sg24664 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9205

lemma sg24665 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8740 sg9453

lemma sg24666 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8721 sg9503

lemma sg24667 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9206

lemma sg24668 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9749

lemma sg24669 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8819 sg9165

lemma sg24670 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8179 sg10857

lemma sg24671 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9749

lemma sg24672 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8543 sg10095

lemma sg24673 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8826 sg9162

lemma sg24674 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5552 sg12620

lemma sg24675 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5249 sg12687

lemma sg24676 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10320

lemma sg24677 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8377 sg10602

lemma sg24678 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8426 sg10236

lemma sg24679 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10320

lemma sg24680 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8558 sg10087

lemma sg24681 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8190 sg10852

lemma sg24682 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9737

lemma sg24683 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9504

lemma sg24684 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8663 sg9668

lemma sg24685 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9750

lemma sg24686 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9750

lemma sg24687 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10243

lemma sg24688 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8663 sg9669

lemma sg24689 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8350 sg10645

lemma sg24690 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6893 sg11495

lemma sg24691 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9751

lemma sg24692 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9751

lemma sg24693 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8740 sg9455

lemma sg24694 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9505

lemma sg24695 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8658 sg9679

lemma sg24696 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg8865 sg8990

lemma sg24697 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg8659 sg9679

lemma sg24698 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10237

lemma sg24699 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10646

lemma sg24700 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,4,4,3] := by
  exact rowSquare_join (by decide) sg8664 sg9669

lemma sg24701 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5265 sg12681

lemma sg24702 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10244

lemma sg24703 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8378 sg10602

lemma sg24704 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9738

lemma sg24705 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9504

lemma sg24706 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8663 sg9670

lemma sg24707 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8379 sg10602

lemma sg24708 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9752

lemma sg24709 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9752

lemma sg24710 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10244

lemma sg24711 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9505

lemma sg24712 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8658 sg9680

lemma sg24713 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8430 sg10236

lemma sg24714 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8350 sg10647

lemma sg24715 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8747 sg9449

lemma sg24716 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9507

lemma sg24717 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8665 sg9668

lemma sg24718 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg8352 sg10645

lemma sg24719 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10238

lemma sg24720 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8659 sg9681

lemma sg24721 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,4,3,3] := by
  exact rowSquare_join (by decide) sg8665 sg9669

lemma sg24722 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10237

lemma sg24723 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,4,4,2] := by
  exact rowSquare_join (by decide) sg8866 sg8993

lemma sg24724 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8527 sg10108

lemma sg24725 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5544 sg12622

lemma sg24726 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg8543 sg10098

lemma sg24727 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg8352 sg10646

lemma sg24728 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,5,3,2] := by
  exact rowSquare_join (by decide) sg8549 sg10090

lemma sg24729 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,6,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7247 sg11440

lemma sg24730 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7252 sg11435

lemma sg24731 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,6,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8657 sg9682

lemma sg24732 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8525 sg10115

lemma sg24733 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8741 sg9456

lemma sg24734 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,6,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8454 sg10195

lemma sg24735 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8736 sg9468

lemma sg24736 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,6,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8665 sg9670

lemma sg24737 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,6,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8461 sg10189

lemma sg24738 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,6,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8658 sg9682

lemma sg24739 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,6,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8659 sg9682

lemma sg24740 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,6,3,3,3] := by
  exact rowSquare_join (by decide) sg7806 sg11241

lemma sg24741 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8455 sg10195

lemma sg24742 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,6,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8456 sg10195

lemma sg24743 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,6,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8457 sg10195

lemma sg24744 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10238

lemma sg24745 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,6,4,3,2] := by
  exact rowSquare_join (by decide) sg8665 sg9671

lemma sg24746 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,6,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg356 sg21295

lemma sg24747 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,6,5,2,1,1] := by
  exact rowSquare_join (by decide) sg8462 sg10189

lemma sg24748 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,6,5,2,2] := by
  exact rowSquare_join (by decide) sg8550 sg10090

lemma sg24749 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg356 sg21296

lemma sg24750 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1319 sg20962

lemma sg24751 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1722 sg18243

lemma sg24752 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1464 sg20933

lemma sg24753 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1817 sg17112

lemma sg24754 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2224 sg15520

lemma sg24755 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1857 sg16195

lemma sg24756 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg571 sg21218

lemma sg24757 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3514 sg14680

lemma sg24758 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg571 sg21219

lemma sg24759 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg571 sg21220

lemma sg24760 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg571 sg21221

lemma sg24761 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1830 sg17105

lemma sg24762 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2197 sg15561

lemma sg24763 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2225 sg15520

lemma sg24764 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2670 sg15014

lemma sg24765 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2867 sg14852

lemma sg24766 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg966 sg21118

lemma sg24767 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2665 sg15023

lemma sg24768 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg966 sg21119

lemma sg24769 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg966 sg21120

lemma sg24770 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2226 sg15520

lemma sg24771 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2671 sg15014

lemma sg24772 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1815 sg17113

lemma sg24773 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3894 sg14498

lemma sg24774 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1293 sg20995

lemma sg24775 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6119 sg11763

lemma sg24776 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1293 sg20996

lemma sg24777 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8666 sg9663

lemma sg24778 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1850 sg16200

lemma sg24779 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5574 sg12613

lemma sg24780 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4622 sg12944

lemma sg24781 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8228 sg10847

lemma sg24782 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8816 sg9166

lemma sg24783 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8651 sg9740

lemma sg24784 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5266 sg12680

lemma sg24785 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8551 sg10088

lemma sg24786 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8816 sg9167

lemma sg24787 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8666 sg9665

lemma sg24788 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8720 sg9508

lemma sg24789 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8181 sg10854

lemma sg24790 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8666 sg9666

lemma sg24791 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8525 sg10116

lemma sg24792 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8219 sg10850

lemma sg24793 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8847 sg9157

lemma sg24794 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2198 sg15561

lemma sg24795 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2227 sg15520

lemma sg24796 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2672 sg15014

lemma sg24797 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2869 sg14851

lemma sg24798 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3895 sg14498

lemma sg24799 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1294 sg20995

lemma sg24800 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7245 sg11442

lemma sg24801 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1294 sg20996

lemma sg24802 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8666 sg9667

lemma sg24803 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2673 sg15014

lemma sg24804 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2180 sg15565

lemma sg24805 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5546 sg12621

lemma sg24806 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5244 sg12688

lemma sg24807 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8229 sg10847

lemma sg24808 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9207

lemma sg24809 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8652 sg9740

lemma sg24810 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5547 sg12621

lemma sg24811 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5245 sg12688

lemma sg24812 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10239

lemma sg24813 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8816 sg9169

lemma sg24814 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8348 sg10648

lemma sg24815 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8721 sg9508

lemma sg24816 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8553 sg10088

lemma sg24817 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8182 sg10854

lemma sg24818 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8660 sg9673

lemma sg24819 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8720 sg9509

lemma sg24820 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8458 sg10190

lemma sg24821 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8525 sg10117

lemma sg24822 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg7232 sg11461

lemma sg24823 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8847 sg9158

lemma sg24824 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2360 sg15482

lemma sg24825 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5576 sg12613

lemma sg24826 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5251 sg12686

lemma sg24827 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8554 sg10088

lemma sg24828 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9208

lemma sg24829 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8666 sg9670

lemma sg24830 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8722 sg9508

lemma sg24831 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5252 sg12686

lemma sg24832 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8555 sg10088

lemma sg24833 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9209

lemma sg24834 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9741

lemma sg24835 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8817 sg9166

lemma sg24836 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9210

lemma sg24837 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9753

lemma sg24838 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9510

lemma sg24839 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8820 sg9163

lemma sg24840 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9753

lemma sg24841 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8820 sg9164

lemma sg24842 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8860 sg9052

lemma sg24843 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7253 sg11433

lemma sg24844 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8394 sg10598

lemma sg24845 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9742

lemma sg24846 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8669 sg9664

lemma sg24847 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8818 sg9166

lemma sg24848 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9754

lemma sg24849 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9754

lemma sg24850 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8818 sg9167

lemma sg24851 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10239

lemma sg24852 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9053

lemma sg24853 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9511

lemma sg24854 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8822 sg9163

lemma sg24855 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9054

lemma sg24856 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg8738 sg9458

lemma sg24857 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg8459 sg10190

lemma sg24858 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2241 sg15512

lemma sg24859 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2685 sg15011

lemma sg24860 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2870 sg14851

lemma sg24861 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5548 sg12621

lemma sg24862 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5246 sg12688

lemma sg24863 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8250 sg10845

lemma sg24864 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9207

lemma sg24865 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8660 sg9674

lemma sg24866 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2871 sg14851

lemma sg24867 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5549 sg12621

lemma sg24868 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5247 sg12688

lemma sg24869 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10240

lemma sg24870 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9211

lemma sg24871 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8349 sg10648

lemma sg24872 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8737 sg9459

lemma sg24873 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5248 sg12688

lemma sg24874 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10241

lemma sg24875 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9209

lemma sg24876 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9744

lemma sg24877 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8721 sg9509

lemma sg24878 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9210

lemma sg24879 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9755

lemma sg24880 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9512

lemma sg24881 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8823 sg9163

lemma sg24882 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9755

lemma sg24883 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8823 sg9164

lemma sg24884 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8860 sg9055

lemma sg24885 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5550 sg12621

lemma sg24886 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5249 sg12688

lemma sg24887 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8557 sg10088

lemma sg24888 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9212

lemma sg24889 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9741

lemma sg24890 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8722 sg9509

lemma sg24891 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10242

lemma sg24892 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9213

lemma sg24893 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9745

lemma sg24894 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9510

lemma sg24895 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8818 sg9168

lemma sg24896 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9756

lemma sg24897 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9756

lemma sg24898 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8663 sg9673

lemma sg24899 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10240

lemma sg24900 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9056

lemma sg24901 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8376 sg10603

lemma sg24902 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9757

lemma sg24903 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9757

lemma sg24904 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8818 sg9169

lemma sg24905 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9513

lemma sg24906 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10241

lemma sg24907 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9057

lemma sg24908 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg8350 sg10649

lemma sg24909 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8869 sg8989

lemma sg24910 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg8738 sg9460

lemma sg24911 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,4,4,3] := by
  exact rowSquare_join (by decide) sg8662 sg9676

lemma sg24912 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5255 sg12686

lemma sg24913 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8559 sg10088

lemma sg24914 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9214

lemma sg24915 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8745 sg9451

lemma sg24916 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9510

lemma sg24917 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8668 sg9670

lemma sg24918 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8395 sg10598

lemma sg24919 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9758

lemma sg24920 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9758

lemma sg24921 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8818 sg9170

lemma sg24922 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9514

lemma sg24923 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8668 sg9671

lemma sg24924 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9058

lemma sg24925 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8741 sg9458

lemma sg24926 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9748

lemma sg24927 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9515

lemma sg24928 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10242

lemma sg24929 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9059

lemma sg24930 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8661 sg9678

lemma sg24931 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8430 sg10239

lemma sg24932 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,4,3,3] := by
  exact rowSquare_join (by decide) sg8459 sg10192

lemma sg24933 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg8864 sg8997

lemma sg24934 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,4,4,2] := by
  exact rowSquare_join (by decide) sg8662 sg9678

lemma sg24935 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8376 sg10604

lemma sg24936 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8372 sg10606

lemma sg24937 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg8352 sg10649

lemma sg24938 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg8864 sg8998

lemma sg24939 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,5,3,2] := by
  exact rowSquare_join (by decide) sg8546 sg10094

end UniversalTensorSquare
end
end

end OAI
