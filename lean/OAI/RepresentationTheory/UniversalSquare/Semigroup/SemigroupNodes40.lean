import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes32
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes37

namespace OAI

/-! Semigroup Nodes 40. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg16540 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,6,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14835

lemma sg16541 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,6,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14836

lemma sg16542 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,6,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg4 sg14602

lemma sg16543 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13627

lemma sg16544 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg14 sg13567

lemma sg16545 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,4,4] := by
  exact rowSquare_join (by decide) sg5 sg14592

lemma sg16546 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,6,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg4 sg14603

lemma sg16547 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,6,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13628

lemma sg16548 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,6,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13629

lemma sg16549 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13630

lemma sg16550 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13631

lemma sg16551 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12736

lemma sg16552 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13632

lemma sg16553 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,3,3,2,2] := by
  exact rowSquare_join (by decide) sg4 sg14604

lemma sg16554 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg4 sg14605

lemma sg16555 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,4,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13633

lemma sg16556 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,4,3,3] := by
  exact rowSquare_join (by decide) sg39 sg12737

lemma sg16557 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg41 sg12724

lemma sg16558 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,5,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13634

lemma sg16559 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,5,3,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12738

lemma sg16560 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,5,5] := by
  exact rowSquare_join (by decide) sg41 sg12727

lemma sg16561 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,6,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13635

lemma sg16562 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,6,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13636

lemma sg16563 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,6,4] := by
  exact rowSquare_join (by decide) sg39 sg12739

lemma sg16564 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,7,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg5 sg14595

lemma sg16565 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,7,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg14 sg13569

lemma sg16566 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,7,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13637

lemma sg16567 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,7,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13638

lemma sg16568 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,7,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg14 sg13576

lemma sg16569 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,7,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg14 sg13577

lemma sg16570 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,7,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13639

lemma sg16571 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,7,5,4,3,3] := by
  exact rowSquare_join (by decide) sg39 sg12740

lemma sg16572 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,7,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg40 sg12736

lemma sg16573 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,7,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13640

lemma sg16574 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,7,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13641

lemma sg16575 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,7,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12741

lemma sg16576 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,7,5,5,5] := by
  exact rowSquare_join (by decide) sg42 sg12727

lemma sg16577 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,7,6,3,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13642

lemma sg16578 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,7,6,3,3,3] := by
  exact rowSquare_join (by decide) sg40 sg12737

lemma sg16579 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,7,6,4,2,2,1] := by
  exact rowSquare_join (by decide) sg39 sg12742

lemma sg16580 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,7,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12743

lemma sg16581 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,7,6,5,2,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12744

lemma sg16582 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,7,6,5,2,2] := by
  exact rowSquare_join (by decide) sg39 sg12745

lemma sg16583 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,7,6,5,4] := by
  exact rowSquare_join (by decide) sg39 sg12746

lemma sg16584 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,7,6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13643

lemma sg16585 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,7,6,6,3] := by
  exact rowSquare_join (by decide) sg39 sg12747

lemma sg16586 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,8,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg14 sg13585

lemma sg16587 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,8,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg14 sg13586

lemma sg16588 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,8,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg14 sg13587

lemma sg16589 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,8,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13644

lemma sg16590 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,8,4,4,3,3] := by
  exact rowSquare_join (by decide) sg39 sg12748

lemma sg16591 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,8,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13592

lemma sg16592 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,8,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13645

lemma sg16593 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,8,5,3,3,3] := by
  exact rowSquare_join (by decide) sg40 sg12740

lemma sg16594 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,8,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg39 sg12749

lemma sg16595 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,8,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12750

lemma sg16596 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,8,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12751

lemma sg16597 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,8,5,5,2,2] := by
  exact rowSquare_join (by decide) sg39 sg12752

lemma sg16598 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,8,5,5,4] := by
  exact rowSquare_join (by decide) sg39 sg12753

lemma sg16599 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,8,6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg13598

lemma sg16600 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,8,6,3,2,2,1] := by
  exact rowSquare_join (by decide) sg39 sg12754

lemma sg16601 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,8,6,3,3,1,1] := by
  exact rowSquare_join (by decide) sg40 sg12743

lemma sg16602 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,8,6,4,2,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12755

lemma sg16603 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,8,6,4,2,2] := by
  exact rowSquare_join (by decide) sg39 sg12756

lemma sg16604 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,8,6,4,4] := by
  exact rowSquare_join (by decide) sg40 sg12746

lemma sg16605 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,8,6,5,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12757

lemma sg16606 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,8,6,5,3] := by
  exact rowSquare_join (by decide) sg39 sg12758

lemma sg16607 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,8,6,6,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12759

lemma sg16608 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,8,6,6,2] := by
  exact rowSquare_join (by decide) sg39 sg12760

lemma sg16609 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,9,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3320 sg4500

lemma sg16610 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,9,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14606

lemma sg16611 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,9,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg14607

lemma sg16612 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,9,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3695 sg4118

lemma sg16613 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,9,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13599

lemma sg16614 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,9,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg14 sg13600

lemma sg16615 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,9,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg14 sg13601

lemma sg16616 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,9,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13646

lemma sg16617 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,9,4,3,3,3] := by
  exact rowSquare_join (by decide) sg40 sg12748

lemma sg16618 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,9,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13647

lemma sg16619 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,9,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13648

lemma sg16620 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,9,5,4,4] := by
  exact rowSquare_join (by decide) sg40 sg12753

lemma sg16621 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [10,4,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14837

lemma sg16622 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [10,4,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg6 sg14586

lemma sg16623 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [10,5,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14838

lemma sg16624 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [10,5,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14839

lemma sg16625 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [10,5,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg4 sg14608

lemma sg16626 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [10,5,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13649

lemma sg16627 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [10,6,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg5 sg14602

lemma sg16628 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [10,6,5,5,5] := by
  exact rowSquare_join (by decide) sg43 sg12727

lemma sg16629 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [10,6,6,5,4] := by
  exact rowSquare_join (by decide) sg51 sg12474

lemma sg16630 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [10,6,6,6,3] := by
  exact rowSquare_join (by decide) sg39 sg12761

lemma sg16631 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [10,7,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13650

lemma sg16632 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [10,7,5,5,4] := by
  exact rowSquare_join (by decide) sg52 sg12474

lemma sg16633 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [10,7,6,4,4] := by
  exact rowSquare_join (by decide) sg51 sg12486

lemma sg16634 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [10,7,6,5,3] := by
  exact rowSquare_join (by decide) sg39 sg12762

lemma sg16635 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [10,7,6,6,2] := by
  exact rowSquare_join (by decide) sg39 sg12763

lemma sg16636 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [10,8,5,4,4] := by
  exact rowSquare_join (by decide) sg52 sg12486

lemma sg16637 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [10,8,5,5,3] := by
  exact rowSquare_join (by decide) sg39 sg12764

lemma sg16638 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [10,8,6,4,3] := by
  exact rowSquare_join (by decide) sg270 sg11069

lemma sg16639 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [10,8,6,5,2] := by
  exact rowSquare_join (by decide) sg270 sg11070

lemma sg16640 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [10,8,6,6,1] := by
  exact rowSquare_join (by decide) sg271 sg11070

lemma sg16641 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [10,9,4,4,4] := by
  exact rowSquare_join (by decide) sg42 sg12753

lemma sg16642 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [10,10,4,4,3] := by
  exact rowSquare_join (by decide) sg13 sg13651

lemma sg16643 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [11,5,5,5,5] := by
  exact rowSquare_join (by decide) sg44 sg12727

lemma sg16644 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [11,6,5,5,4] := by
  exact rowSquare_join (by decide) sg53 sg12474

lemma sg16645 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [11,6,6,4,4] := by
  exact rowSquare_join (by decide) sg270 sg11087

lemma sg16646 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [11,6,6,5,3] := by
  exact rowSquare_join (by decide) sg270 sg11089

lemma sg16647 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [11,6,6,6,2] := by
  exact rowSquare_join (by decide) sg271 sg11089

lemma sg16648 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [11,8,4,4,4] := by
  exact rowSquare_join (by decide) sg111 sg11615

lemma sg16649 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1682 sg6504

lemma sg16650 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg6497

lemma sg16651 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2633 sg4964

lemma sg16652 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3691 sg4067

lemma sg16653 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3691 sg4068

lemma sg16654 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg3691 sg4070

lemma sg16655 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,3,3] := by
  exact rowSquare_join (by decide) sg2633 sg4967

lemma sg16656 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,4,2] := by
  exact rowSquare_join (by decide) sg1758 sg6498

lemma sg16657 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,3,3] := by
  exact rowSquare_join (by decide) sg3355 sg4437

lemma sg16658 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,4,2] := by
  exact rowSquare_join (by decide) sg3560 sg4303

lemma sg16659 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15502

lemma sg16660 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,3,2] := by
  exact rowSquare_join (by decide) sg3560 sg4304

lemma sg16661 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,4,1] := by
  exact rowSquare_join (by decide) sg1758 sg6499

lemma sg16662 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3691 sg4074

lemma sg16663 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,4,2] := by
  exact rowSquare_join (by decide) sg4 sg14611

lemma sg16664 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,3,3,3] := by
  exact rowSquare_join (by decide) sg3352 sg4441

lemma sg16665 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,4,3,2] := by
  exact rowSquare_join (by decide) sg3653 sg4157

lemma sg16666 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,4,4,1] := by
  exact rowSquare_join (by decide) sg3562 sg4303

lemma sg16667 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3691 sg4075

lemma sg16668 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,2,2] := by
  exact rowSquare_join (by decide) sg3691 sg4076

lemma sg16669 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,3,1] := by
  exact rowSquare_join (by decide) sg3562 sg4304

lemma sg16670 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,4] := by
  exact rowSquare_join (by decide) sg1688 sg6505

lemma sg16671 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14612

lemma sg16672 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,3,2] := by
  exact rowSquare_join (by decide) sg4 sg14613

lemma sg16673 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,4,1] := by
  exact rowSquare_join (by decide) sg3620 sg4185

lemma sg16674 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,3,3,2] := by
  exact rowSquare_join (by decide) sg4 sg14614

lemma sg16675 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,4,2,2] := by
  exact rowSquare_join (by decide) sg4 sg14615

lemma sg16676 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,4,3,1] := by
  exact rowSquare_join (by decide) sg3689 sg4079

lemma sg16677 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,4,4] := by
  exact rowSquare_join (by decide) sg1688 sg6506

lemma sg16678 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14616

lemma sg16679 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,5,2,1] := by
  exact rowSquare_join (by decide) sg3723 sg4031

lemma sg16680 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,5,3] := by
  exact rowSquare_join (by decide) sg3356 sg4438

lemma sg16681 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3571 sg4226

lemma sg16682 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3613 sg4188

lemma sg16683 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,3,2,2] := by
  exact rowSquare_join (by decide) sg3654 sg4157

lemma sg16684 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,3,3,1] := by
  exact rowSquare_join (by decide) sg3565 sg4303

lemma sg16685 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,4,1,1,1] := by
  exact rowSquare_join (by decide) sg3691 sg4077

lemma sg16686 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,4,2,1] := by
  exact rowSquare_join (by decide) sg3724 sg4031

lemma sg16687 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,4,3] := by
  exact rowSquare_join (by decide) sg3690 sg4079

lemma sg16688 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,5,1,1] := by
  exact rowSquare_join (by decide) sg3655 sg4157

lemma sg16689 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,5,2] := by
  exact rowSquare_join (by decide) sg3725 sg4031

lemma sg16690 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,6,1] := by
  exact rowSquare_join (by decide) sg3726 sg4031

lemma sg16691 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg3560 sg4305

lemma sg16692 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg5 sg14609

lemma sg16693 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,4,3,3] := by
  exact rowSquare_join (by decide) sg4 sg14617

lemma sg16694 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,4,4,2] := by
  exact rowSquare_join (by decide) sg9 sg13654

lemma sg16695 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,3,3,3] := by
  exact rowSquare_join (by decide) sg3560 sg4306

lemma sg16696 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,4,3,2] := by
  exact rowSquare_join (by decide) sg1 sg14840

lemma sg16697 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,4,4,1] := by
  exact rowSquare_join (by decide) sg1 sg14841

lemma sg16698 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14842

lemma sg16699 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,3,1] := by
  exact rowSquare_join (by decide) sg1 sg14843

lemma sg16700 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,4] := by
  exact rowSquare_join (by decide) sg2167 sg5763

lemma sg16701 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg5 sg14610

lemma sg16702 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg10 sg13654

lemma sg16703 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,4,3,2] := by
  exact rowSquare_join (by decide) sg9 sg13657

lemma sg16704 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,4,4,1] := by
  exact rowSquare_join (by decide) sg9 sg13658

lemma sg16705 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,3,3,2] := by
  exact rowSquare_join (by decide) sg5 sg14614

lemma sg16706 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,4,2,2] := by
  exact rowSquare_join (by decide) sg5 sg14615

lemma sg16707 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,4,3,1] := by
  exact rowSquare_join (by decide) sg0 sg15503

lemma sg16708 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,4,4] := by
  exact rowSquare_join (by decide) sg0 sg15504

lemma sg16709 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg0 sg15505

lemma sg16710 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,5,3] := by
  exact rowSquare_join (by decide) sg0 sg15506

lemma sg16711 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,3,3,3,3] := by
  exact rowSquare_join (by decide) sg9 sg13661

lemma sg16712 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,3,3,2] := by
  exact rowSquare_join (by decide) sg9 sg13662

lemma sg16713 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,4,2,2] := by
  exact rowSquare_join (by decide) sg9 sg13664

lemma sg16714 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,4,3,1] := by
  exact rowSquare_join (by decide) sg9 sg13665

lemma sg16715 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,4,4] := by
  exact rowSquare_join (by decide) sg0 sg15507

lemma sg16716 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,3,2,2] := by
  exact rowSquare_join (by decide) sg9 sg13667

lemma sg16717 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,3,3,1] := by
  exact rowSquare_join (by decide) sg9 sg13668

lemma sg16718 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12765

lemma sg16719 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,4,2,1] := by
  exact rowSquare_join (by decide) sg26 sg12766

lemma sg16720 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,4,3] := by
  exact rowSquare_join (by decide) sg0 sg15508

lemma sg16721 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,5,1,1] := by
  exact rowSquare_join (by decide) sg9 sg13671

lemma sg16722 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,5,2] := by
  exact rowSquare_join (by decide) sg74 sg12341

lemma sg16723 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15509

lemma sg16724 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,2,2,2] := by
  exact rowSquare_join (by decide) sg3560 sg4311

lemma sg16725 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,3,1,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12767

lemma sg16726 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,3,2,1] := by
  exact rowSquare_join (by decide) sg26 sg12768

lemma sg16727 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15510

lemma sg16728 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,4,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12769

lemma sg16729 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,4,2] := by
  exact rowSquare_join (by decide) sg74 sg12342

lemma sg16730 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,5,1] := by
  exact rowSquare_join (by decide) sg74 sg12343

lemma sg16731 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,6] := by
  exact rowSquare_join (by decide) sg0 sg15511

lemma sg16732 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg3696 sg4076

lemma sg16733 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg10 sg13657

lemma sg16734 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg10 sg13658

lemma sg16735 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg10 sg13662

lemma sg16736 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg10 sg13664

lemma sg16737 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg10 sg13665

lemma sg16738 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,4,4] := by
  exact rowSquare_join (by decide) sg2746 sg4896

lemma sg16739 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg10 sg13667

lemma sg16740 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg10 sg13668

lemma sg16741 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg10 sg13670

lemma sg16742 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,4,3] := by
  exact rowSquare_join (by decide) sg3725 sg4032

lemma sg16743 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg10 sg13671

lemma sg16744 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,5,2] := by
  exact rowSquare_join (by decide) sg74 sg12344

lemma sg16745 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,3,3,3,2] := by
  exact rowSquare_join (by decide) sg4 sg14619

lemma sg16746 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,4,3,2,2] := by
  exact rowSquare_join (by decide) sg4 sg14620

lemma sg16747 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,4,3,3,1] := by
  exact rowSquare_join (by decide) sg4 sg14621

lemma sg16748 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,4,4,2,1] := by
  exact rowSquare_join (by decide) sg27 sg12766

lemma sg16749 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,4,4,3] := by
  exact rowSquare_join (by decide) sg3620 sg4187

lemma sg16750 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3686 sg4082

lemma sg16751 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg14622

lemma sg16752 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,3,2,1] := by
  exact rowSquare_join (by decide) sg27 sg12768

lemma sg16753 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,3,3] := by
  exact rowSquare_join (by decide) sg4 sg14623

lemma sg16754 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,4,1,1] := by
  exact rowSquare_join (by decide) sg27 sg12769

lemma sg16755 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,4,2] := by
  exact rowSquare_join (by decide) sg74 sg12345

lemma sg16756 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,5,1] := by
  exact rowSquare_join (by decide) sg74 sg12346

lemma sg16757 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3686 sg4083

lemma sg16758 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3687 sg4083

lemma sg16759 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,2,2,1] := by
  exact rowSquare_join (by decide) sg3617 sg4188

lemma sg16760 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,3,1,1] := by
  exact rowSquare_join (by decide) sg3724 sg4033

lemma sg16761 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,3,2] := by
  exact rowSquare_join (by decide) sg74 sg12347

lemma sg16762 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,4,1] := by
  exact rowSquare_join (by decide) sg74 sg12348

lemma sg16763 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,5] := by
  exact rowSquare_join (by decide) sg3726 sg4033

lemma sg16764 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3721 sg4037

lemma sg16765 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg14624

lemma sg16766 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4189

lemma sg16767 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg14625

lemma sg16768 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3721 sg4038

lemma sg16769 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14626

lemma sg16770 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,3,2,2] := by
  exact rowSquare_join (by decide) sg4 sg14627

lemma sg16771 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,3,3,1] := by
  exact rowSquare_join (by decide) sg4 sg14628

lemma sg16772 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3721 sg4039

lemma sg16773 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14629

lemma sg16774 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg14630

lemma sg16775 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14631

lemma sg16776 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,3,2,1] := by
  exact rowSquare_join (by decide) sg4 sg14632

lemma sg16777 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,3,3] := by
  exact rowSquare_join (by decide) sg4 sg14633

lemma sg16778 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,4,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14634

lemma sg16779 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,4,2] := by
  exact rowSquare_join (by decide) sg74 sg12349

lemma sg16780 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3688 sg4083

lemma sg16781 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14635

lemma sg16782 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg14636

lemma sg16783 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,3,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14637

lemma sg16784 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,3,2] := by
  exact rowSquare_join (by decide) sg74 sg12350

lemma sg16785 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,4,1] := by
  exact rowSquare_join (by decide) sg74 sg12351

lemma sg16786 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,5] := by
  exact rowSquare_join (by decide) sg4 sg14638

lemma sg16787 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3575 sg4226

lemma sg16788 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14639

lemma sg16789 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,2,2] := by
  exact rowSquare_join (by decide) sg74 sg12352

lemma sg16790 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,3,1] := by
  exact rowSquare_join (by decide) sg74 sg12353

lemma sg16791 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,4] := by
  exact rowSquare_join (by decide) sg4 sg14640

lemma sg16792 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,7,1,1,1] := by
  exact rowSquare_join (by decide) sg3565 sg4311

lemma sg16793 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,7,2,1] := by
  exact rowSquare_join (by decide) sg74 sg12354

lemma sg16794 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,7,3] := by
  exact rowSquare_join (by decide) sg3691 sg4083

lemma sg16795 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg6 sg14609

lemma sg16796 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg5 sg14617

lemma sg16797 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg11 sg13654

lemma sg16798 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,3,3,3] := by
  exact rowSquare_join (by decide) sg4 sg14641

lemma sg16799 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,4,3,2] := by
  exact rowSquare_join (by decide) sg9 sg13678

lemma sg16800 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,4,4,1] := by
  exact rowSquare_join (by decide) sg9 sg13679

lemma sg16801 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,3,3,2] := by
  exact rowSquare_join (by decide) sg6 sg14614

lemma sg16802 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,2,2] := by
  exact rowSquare_join (by decide) sg6 sg14615

lemma sg16803 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,3,1] := by
  exact rowSquare_join (by decide) sg26 sg12772

lemma sg16804 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,4] := by
  exact rowSquare_join (by decide) sg1 sg14844

lemma sg16805 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg3 sg14648

lemma sg16806 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,5,3] := by
  exact rowSquare_join (by decide) sg74 sg12355

lemma sg16807 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg5 sg14618

lemma sg16808 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg10 sg13678

lemma sg16809 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg10 sg13679

lemma sg16810 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg9 sg13684

lemma sg16811 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg9 sg13685

lemma sg16812 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg9 sg13687

lemma sg16813 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg27 sg12772

lemma sg16814 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,4] := by
  exact rowSquare_join (by decide) sg9 sg13689

lemma sg16815 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg11 sg13667

lemma sg16816 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg26 sg12773

lemma sg16817 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg26 sg12774

lemma sg16818 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,4,3] := by
  exact rowSquare_join (by decide) sg74 sg12356

lemma sg16819 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg11 sg13671

lemma sg16820 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,5,2] := by
  exact rowSquare_join (by decide) sg74 sg12357

lemma sg16821 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,3,3,3,2] := by
  exact rowSquare_join (by decide) sg22 sg12817

lemma sg16822 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,3,2,2] := by
  exact rowSquare_join (by decide) sg26 sg12776

lemma sg16823 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,3,3,1] := by
  exact rowSquare_join (by decide) sg26 sg12777

lemma sg16824 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,4,2,1] := by
  exact rowSquare_join (by decide) sg74 sg12358

lemma sg16825 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,4,3] := by
  exact rowSquare_join (by decide) sg74 sg12359

lemma sg16826 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,2,2,2] := by
  exact rowSquare_join (by decide) sg26 sg12778

lemma sg16827 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,3,2,1] := by
  exact rowSquare_join (by decide) sg74 sg12360

lemma sg16828 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,3,3] := by
  exact rowSquare_join (by decide) sg74 sg12361

lemma sg16829 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,4,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12779

lemma sg16830 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,4,2] := by
  exact rowSquare_join (by decide) sg74 sg12362

lemma sg16831 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,5,1] := by
  exact rowSquare_join (by decide) sg74 sg12363

lemma sg16832 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14845

lemma sg16833 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,2,2,1] := by
  exact rowSquare_join (by decide) sg26 sg12780

lemma sg16834 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,3,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12781

lemma sg16835 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,3,2] := by
  exact rowSquare_join (by decide) sg74 sg12364

lemma sg16836 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,4,1] := by
  exact rowSquare_join (by decide) sg74 sg12365

lemma sg16837 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,5] := by
  exact rowSquare_join (by decide) sg75 sg12343

lemma sg16838 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg9 sg13711

lemma sg16839 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg10 sg13685

lemma sg16840 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg10 sg13687

lemma sg16841 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg10 sg13688

lemma sg16842 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,4] := by
  exact rowSquare_join (by decide) sg10 sg13689

lemma sg16843 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg23 sg12817

lemma sg16844 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg26 sg12782

lemma sg16845 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg26 sg12783

lemma sg16846 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg74 sg12366

lemma sg16847 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,4,3] := by
  exact rowSquare_join (by decide) sg74 sg12367

lemma sg16848 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg23 sg12818

lemma sg16849 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg26 sg12784

lemma sg16850 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,3,3] := by
  exact rowSquare_join (by decide) sg74 sg12368

lemma sg16851 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12786

lemma sg16852 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,4,2] := by
  exact rowSquare_join (by decide) sg74 sg12369

lemma sg16853 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,5,1] := by
  exact rowSquare_join (by decide) sg74 sg12370

lemma sg16854 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,3,3,2,2] := by
  exact rowSquare_join (by decide) sg27 sg12776

lemma sg16855 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg27 sg12777

lemma sg16856 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,2,2,2] := by
  exact rowSquare_join (by decide) sg26 sg12788

lemma sg16857 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,3,2,1] := by
  exact rowSquare_join (by decide) sg74 sg12371

lemma sg16858 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,3,3] := by
  exact rowSquare_join (by decide) sg74 sg12372

lemma sg16859 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg27 sg12779

lemma sg16860 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,4,2] := by
  exact rowSquare_join (by decide) sg74 sg12373

lemma sg16861 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14642

lemma sg16862 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg12374

lemma sg16863 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,3,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12789

lemma sg16864 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,3,2] := by
  exact rowSquare_join (by decide) sg74 sg12375

lemma sg16865 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,4,1] := by
  exact rowSquare_join (by decide) sg74 sg12376

lemma sg16866 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,5] := by
  exact rowSquare_join (by decide) sg75 sg12346

lemma sg16867 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,6,2,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12790

lemma sg16868 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,6,2,2] := by
  exact rowSquare_join (by decide) sg74 sg12377

lemma sg16869 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,6,3,1] := by
  exact rowSquare_join (by decide) sg74 sg12378

lemma sg16870 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,6,4] := by
  exact rowSquare_join (by decide) sg75 sg12348

lemma sg16871 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg10 sg13709

lemma sg16872 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg10 sg13710

lemma sg16873 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg10 sg13711

lemma sg16874 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg10 sg13712

lemma sg16875 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg10 sg13713

lemma sg16876 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg10 sg13714

lemma sg16877 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg10 sg13715

lemma sg16878 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg10 sg13716

lemma sg16879 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg10 sg13717

lemma sg16880 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg10 sg13718

lemma sg16881 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg10 sg13719

lemma sg16882 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg13720

lemma sg16883 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg10 sg13721

lemma sg16884 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,4,3] := by
  exact rowSquare_join (by decide) sg74 sg12379

lemma sg16885 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg27 sg12783

lemma sg16886 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg74 sg12380

lemma sg16887 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,4,3,3] := by
  exact rowSquare_join (by decide) sg74 sg12381

lemma sg16888 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg27 sg12786

lemma sg16889 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,4,4,2] := by
  exact rowSquare_join (by decide) sg74 sg12382

lemma sg16890 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3686 sg4084

lemma sg16891 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg10 sg13735

lemma sg16892 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg10 sg13736

lemma sg16893 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,5,3,2] := by
  exact rowSquare_join (by decide) sg74 sg12383

lemma sg16894 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,5,4,1] := by
  exact rowSquare_join (by decide) sg74 sg12384

lemma sg16895 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,5,5] := by
  exact rowSquare_join (by decide) sg10 sg13739

lemma sg16896 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,3,3,2,1] := by
  exact rowSquare_join (by decide) sg74 sg12385

lemma sg16897 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,3,3,3] := by
  exact rowSquare_join (by decide) sg74 sg12386

lemma sg16898 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3686 sg4085

lemma sg16899 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,4,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg12387

lemma sg16900 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg55 sg12443

lemma sg16901 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,4,3,2] := by
  exact rowSquare_join (by decide) sg74 sg12388

lemma sg16902 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,4,4,1] := by
  exact rowSquare_join (by decide) sg74 sg12389

lemma sg16903 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,5,2,1,1] := by
  exact rowSquare_join (by decide) sg27 sg12790

lemma sg16904 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,5,2,2] := by
  exact rowSquare_join (by decide) sg74 sg12390

lemma sg16905 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,5,3,1] := by
  exact rowSquare_join (by decide) sg74 sg12391

lemma sg16906 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,5,4] := by
  exact rowSquare_join (by decide) sg76 sg12346

lemma sg16907 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg13756

lemma sg16908 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,6,2,1] := by
  exact rowSquare_join (by decide) sg74 sg12392

lemma sg16909 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,6,3] := by
  exact rowSquare_join (by decide) sg76 sg12348

lemma sg16910 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg6 sg14617

lemma sg16911 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg12 sg13654

lemma sg16912 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg5 sg14641

lemma sg16913 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg11 sg13678

lemma sg16914 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg11 sg13679

lemma sg16915 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg9 sg13765

lemma sg16916 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg26 sg12791

lemma sg16917 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg22 sg12820

lemma sg16918 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg74 sg12393

lemma sg16919 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,4,4] := by
  exact rowSquare_join (by decide) sg74 sg12394

lemma sg16920 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg12 sg13667

lemma sg16921 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg26 sg12792

lemma sg16922 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg26 sg12793

lemma sg16923 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,4,3] := by
  exact rowSquare_join (by decide) sg74 sg12395

lemma sg16924 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg12 sg13671

lemma sg16925 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg74 sg12396

lemma sg16926 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg9 sg13780

lemma sg16927 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg23 sg12819

lemma sg16928 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg23 sg12820

lemma sg16929 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg29 sg12772

lemma sg16930 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,4,4] := by
  exact rowSquare_join (by decide) sg74 sg12397

lemma sg16931 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg27 sg12791

lemma sg16932 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg26 sg12794

lemma sg16933 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg12398

lemma sg16934 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg74 sg12399

lemma sg16935 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,4,4,3] := by
  exact rowSquare_join (by decide) sg74 sg12400

lemma sg16936 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg26 sg12795

lemma sg16937 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg74 sg12401

lemma sg16938 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,3,3] := by
  exact rowSquare_join (by decide) sg74 sg12402

lemma sg16939 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12796

end UniversalTensorSquare
end
end

end OAI
