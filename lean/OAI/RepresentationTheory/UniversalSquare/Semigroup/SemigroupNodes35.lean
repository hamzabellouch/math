import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes18
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes16
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes17
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes26
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes34

namespace OAI

/-! Semigroup Nodes 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14540 : RowSquare [9,7,2,1,1,1,1,1,1,1,1,1] [5,4,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg738 sg4930

lemma sg14541 : RowSquare [9,7,2,1,1,1,1,1,1,1,1,1] [5,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg739 sg4930

lemma sg14542 : RowSquare [9,7,2,1,1,1,1,1,1,1,1,1] [5,5,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg740 sg4930

lemma sg14543 : RowSquare [9,7,2,1,1,1,1,1,1,1,1,1] [5,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg741 sg4930

lemma sg14544 : RowSquare [9,7,2,1,1,1,1,1,1,1,1,1] [6,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg747 sg4930

lemma sg14545 : RowSquare [9,7,2,1,1,1,1,1,1,1,1,1] [6,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg748 sg4930

lemma sg14546 : RowSquare [9,7,3,2,1,1,1,1,1,1] [8,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg109 sg7998

lemma sg14547 : RowSquare [9,7,3,2,1,1,1,1,1,1] [9,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg109 sg7999

lemma sg14548 : RowSquare [11,3,2,2,2,2,2,2,1] [6,6,5,5,5] := by
  exact rowSquare_join (by decide) sg166 sg7538

lemma sg14549 : RowSquare [11,3,3,2,2,2,2,1,1] [5,5,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg306 sg6346

lemma sg14550 : RowSquare [11,3,3,2,2,2,2,2] [5,5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg310 sg6178

lemma sg14551 : RowSquare [12,4,2,2,2,2,2,1] [6,6,5,5,5] := by
  exact rowSquare_join (by decide) sg143 sg6919

lemma sg14552 : RowSquare [12,4,2,2,2,2,2,1] [7,7,4,4,4,1] := by
  exact rowSquare_join (by decide) sg143 sg6948

lemma sg14553 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg2925 sg2837

lemma sg14554 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg2925 sg2838

lemma sg14555 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2839 sg2925

lemma sg14556 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,3,3,2] := by
  exact rowSquare_join (by decide) sg2925 sg2840

lemma sg14557 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg2310 sg3648

lemma sg14558 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg2311 sg3648

lemma sg14559 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg2925 sg2843

lemma sg14560 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg2925 sg2844

lemma sg14561 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg2925 sg2845

lemma sg14562 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg2925 sg2846

lemma sg14563 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg2769 sg3004

lemma sg14564 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2925 sg2847

lemma sg14565 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2394 sg3502

lemma sg14566 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg3000 sg2772

lemma sg14567 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg2925 sg2848

lemma sg14568 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg3001 sg2772

lemma sg14569 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1698 sg4539

lemma sg14570 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1518 sg4928

lemma sg14571 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2395 sg3502

lemma sg14572 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg2390 sg3505

lemma sg14573 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg2314 sg3648

lemma sg14574 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2925 sg2849

lemma sg14575 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2662 sg3128

lemma sg14576 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2212 sg3709

lemma sg14577 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg3003 sg2772

lemma sg14578 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,3] := by
  exact rowSquare_join (by decide) sg3004 sg2772

lemma sg14579 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg3005 sg2772

lemma sg14580 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2925 sg2853

lemma sg14581 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2311 sg3649

lemma sg14582 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2393 sg3505

lemma sg14583 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,2] := by
  exact rowSquare_join (by decide) sg3007 sg2772

lemma sg14584 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1735 sg4526

lemma sg14585 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,5] := by
  exact rowSquare_join (by decide) sg2432 sg3420

lemma sg14586 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg2925 sg2854

lemma sg14587 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg2925 sg2855

lemma sg14588 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg3001 sg2774

lemma sg14589 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2925 sg2856

lemma sg14590 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg2925 sg2857

lemma sg14591 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg3001 sg2775

lemma sg14592 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg2838 sg2930

lemma sg14593 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2925 sg2858

lemma sg14594 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,4,3] := by
  exact rowSquare_join (by decide) sg3012 sg2772

lemma sg14595 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2925 sg2860

lemma sg14596 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2925 sg2861

lemma sg14597 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg3001 sg2778

lemma sg14598 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,4,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2842 sg2930

lemma sg14599 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,4,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2925 sg2862

lemma sg14600 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2326 sg3648

lemma sg14601 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg2844 sg2930

lemma sg14602 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2925 sg2863

lemma sg14603 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2925 sg2864

lemma sg14604 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2925 sg2865

lemma sg14605 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg3001 sg2782

lemma sg14606 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2216 sg3720

lemma sg14607 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3020 sg2776

lemma sg14608 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2925 sg2866

lemma sg14609 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg2925 sg2799

lemma sg14610 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg2925 sg2801

lemma sg14611 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg2925 sg2802

lemma sg14612 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg849 sg5792

lemma sg14613 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,4,3,2] := by
  exact rowSquare_join (by decide) sg2925 sg2805

lemma sg14614 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,3,3,2] := by
  exact rowSquare_join (by decide) sg2925 sg2806

lemma sg14615 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,4,2,2] := by
  exact rowSquare_join (by decide) sg2925 sg2807

lemma sg14616 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg1033 sg5772

lemma sg14617 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg2925 sg2809

lemma sg14618 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg2925 sg2811

lemma sg14619 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2925 sg2818

lemma sg14620 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg2925 sg2819

lemma sg14621 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg2928 sg2802

lemma sg14622 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg2925 sg2820

lemma sg14623 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,3,3] := by
  exact rowSquare_join (by decide) sg1032 sg5773

lemma sg14624 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3005 sg2762

lemma sg14625 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3005 sg2763

lemma sg14626 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2798 sg2941

lemma sg14627 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2925 sg2821

lemma sg14628 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2311 sg3644

lemma sg14629 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2798 sg2942

lemma sg14630 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,2,2,2] := by
  exact rowSquare_join (by decide) sg2925 sg2822

lemma sg14631 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2762 sg3009

lemma sg14632 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,3,2,1] := by
  exact rowSquare_join (by decide) sg2928 sg2805

lemma sg14633 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,3,3] := by
  exact rowSquare_join (by decide) sg1032 sg5774

lemma sg14634 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2405 sg3420

lemma sg14635 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2310 sg3645

lemma sg14636 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,2,2,1] := by
  exact rowSquare_join (by decide) sg2928 sg2806

lemma sg14637 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,3,1,1] := by
  exact rowSquare_join (by decide) sg2928 sg2807

lemma sg14638 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,5] := by
  exact rowSquare_join (by decide) sg2407 sg3420

lemma sg14639 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,2,1,1] := by
  exact rowSquare_join (by decide) sg2395 sg3500

lemma sg14640 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,4] := by
  exact rowSquare_join (by decide) sg1033 sg5775

lemma sg14641 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg2925 sg2824

lemma sg14642 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg850 sg5793

lemma sg14643 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,3,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2831 sg2925

lemma sg14644 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1] [5,4,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg2925 sg2615

lemma sg14645 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1] [5,5,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg2111 sg3702

lemma sg14646 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1] [6,5,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg2111 sg3704

lemma sg14647 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg2310 sg3622

lemma sg14648 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg2311 sg3622

lemma sg14649 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1289 sg4997

lemma sg14650 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2902 sg2810

lemma sg14651 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,4] := by
  exact rowSquare_join (by decide) sg2314 sg3620

lemma sg14652 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg2314 sg3622

lemma sg14653 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,4] := by
  exact rowSquare_join (by decide) sg3004 sg2746

lemma sg14654 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,3] := by
  exact rowSquare_join (by decide) sg3004 sg2747

lemma sg14655 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,3,3] := by
  exact rowSquare_join (by decide) sg3004 sg2748

lemma sg14656 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2173 sg3699

lemma sg14657 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2341 sg3563

lemma sg14658 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg2821

lemma sg14659 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2798 sg2922

lemma sg14660 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2341 sg3564

lemma sg14661 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2311 sg3629

lemma sg14662 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2405 sg3411

lemma sg14663 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,2] := by
  exact rowSquare_join (by decide) sg3007 sg2747

lemma sg14664 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2310 sg3630

lemma sg14665 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,5] := by
  exact rowSquare_join (by decide) sg2407 sg3411

lemma sg14666 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1686 sg4539

lemma sg14667 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,2,2] := by
  exact rowSquare_join (by decide) sg3008 sg2748

lemma sg14668 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,3,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2326 sg3614

lemma sg14669 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2902 sg2823

lemma sg14670 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2903 sg2808

lemma sg14671 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2903 sg2810

lemma sg14672 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2663 sg3110

lemma sg14673 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg2826

lemma sg14674 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2663 sg3111

lemma sg14675 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2370 sg3508

lemma sg14676 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,3,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2902 sg2831

lemma sg14677 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2808 sg2909

lemma sg14678 : RowSquare [5,4,3,3,2,2,2,2,2,2,1] [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2250 sg3299

lemma sg14679 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1,1] [7,5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg3004 sg2651

lemma sg14680 : RowSquare [5,5,2,2,2,2,2,2,2,2,1,1] [5,5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1931 sg3998

lemma sg14681 : RowSquare [5,5,2,2,2,2,2,2,2,2,1,1] [6,5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1934 sg3998

lemma sg14682 : RowSquare [5,5,2,2,2,2,2,2,2,2,1,1] [6,5,4,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1930 sg3999

lemma sg14683 : RowSquare [5,5,2,2,2,2,2,2,2,2,1,1] [6,5,5,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1931 sg3999

lemma sg14684 : RowSquare [5,5,2,2,2,2,2,2,2,2,1,1] [6,6,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1935 sg3998

lemma sg14685 : RowSquare [5,5,2,2,2,2,2,2,2,2,1,1] [6,6,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1936 sg3998

lemma sg14686 : RowSquare [5,5,2,2,2,2,2,2,2,2,1,1] [7,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1937 sg3998

lemma sg14687 : RowSquare [5,5,2,2,2,2,2,2,2,2,1,1] [7,4,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1938 sg3998

lemma sg14688 : RowSquare [5,5,2,2,2,2,2,2,2,2,1,1] [7,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1939 sg3998

lemma sg14689 : RowSquare [5,5,2,2,2,2,2,2,2,2,1,1] [7,5,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1940 sg3998

lemma sg14690 : RowSquare [5,5,2,2,2,2,2,2,2,2,1,1] [7,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1941 sg3998

lemma sg14691 : RowSquare [5,5,2,2,2,2,2,2,2,2,1,1] [7,6,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1942 sg3998

lemma sg14692 : RowSquare [5,5,2,2,2,2,2,2,2,2,1,1] [7,6,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1935 sg3999

lemma sg14693 : RowSquare [5,5,2,2,2,2,2,2,2,2,1,1] [7,6,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1936 sg3999

lemma sg14694 : RowSquare [5,5,2,2,2,2,2,2,2,2,1,1] [7,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1943 sg3998

lemma sg14695 : RowSquare [5,5,3,2,2,2,2,2,2,2,1] [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1854 sg3998

lemma sg14696 : RowSquare [5,5,3,2,2,2,2,2,2,2,1] [6,6,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1488 sg4832

lemma sg14697 : RowSquare [5,5,3,2,2,2,2,2,2,2,1] [7,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1867 sg3998

lemma sg14698 : RowSquare [5,5,3,3,2,2,2,2,2,1,1] [7,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1476 sg4832

lemma sg14699 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1] [5,4,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2144 sg3614

lemma sg14700 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1] [5,5,5,4,4,4,1] := by
  exact rowSquare_join (by decide) sg2141 sg3620

lemma sg14701 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1] [6,4,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2144 sg3615

lemma sg14702 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1] [6,5,5,4,4,4] := by
  exact rowSquare_join (by decide) sg2144 sg3620

lemma sg14703 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1] [7,5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg2746 sg2651

lemma sg14704 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1] [8,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg2752 sg2651

lemma sg14705 : RowSquare [6,4,3,2,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg4508

lemma sg14706 : RowSquare [6,4,3,2,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1757 sg4506

lemma sg14707 : RowSquare [6,4,3,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1757 sg4508

lemma sg14708 : RowSquare [6,5,2,2,2,2,2,2,2,2,1] [5,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg996 sg5672

lemma sg14709 : RowSquare [6,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1757 sg4493

lemma sg14710 : RowSquare [6,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,5,3,3] := by
  exact rowSquare_join (by decide) sg1765 sg4488

lemma sg14711 : RowSquare [6,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1757 sg4496

lemma sg14712 : RowSquare [6,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,6,2,2] := by
  exact rowSquare_join (by decide) sg1000 sg5771

lemma sg14713 : RowSquare [6,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2721 sg2921

lemma sg14714 : RowSquare [6,5,3,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg991 sg5672

lemma sg14715 : RowSquare [6,5,3,2,2,2,2,2,2,1,1] [6,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg663 sg6457

lemma sg14716 : RowSquare [6,5,3,2,2,2,2,2,2,1,1] [6,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg992 sg5672

lemma sg14717 : RowSquare [6,5,3,2,2,2,2,2,2,1,1] [6,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg664 sg6457

lemma sg14718 : RowSquare [6,5,3,2,2,2,2,2,2,1,1] [6,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg666 sg6457

lemma sg14719 : RowSquare [6,5,3,2,2,2,2,2,2,1,1] [6,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg993 sg5672

lemma sg14720 : RowSquare [6,5,3,2,2,2,2,2,2,1,1] [7,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg667 sg6457

lemma sg14721 : RowSquare [6,5,3,2,2,2,2,2,2,1,1] [7,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg994 sg5672

lemma sg14722 : RowSquare [6,5,3,2,2,2,2,2,2,1,1] [7,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg668 sg6457

lemma sg14723 : RowSquare [6,5,3,2,2,2,2,2,2,1,1] [7,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg669 sg6457

lemma sg14724 : RowSquare [6,5,3,3,2,2,1,1,1,1,1,1,1] [5,4,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg14310

lemma sg14725 : RowSquare [6,5,3,3,2,2,1,1,1,1,1,1,1] [5,5,5,4,4,4,1] := by
  exact rowSquare_join (by decide) sg1688 sg4377

lemma sg14726 : RowSquare [6,5,3,3,2,2,1,1,1,1,1,1,1] [5,5,5,5,4,4] := by
  exact rowSquare_join (by decide) sg1688 sg4378

lemma sg14727 : RowSquare [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg2273 sg3578

lemma sg14728 : RowSquare [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2887 sg2736

lemma sg14729 : RowSquare [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1330 sg4983

lemma sg14730 : RowSquare [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg4984

lemma sg14731 : RowSquare [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2277 sg3576

lemma sg14732 : RowSquare [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,2] := by
  exact rowSquare_join (by decide) sg1332 sg4984

lemma sg14733 : RowSquare [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg2273 sg3581

lemma sg14734 : RowSquare [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2725 sg2891

lemma sg14735 : RowSquare [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,5,4,2] := by
  exact rowSquare_join (by decide) sg2278 sg3578

lemma sg14736 : RowSquare [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg2273 sg3589

lemma sg14737 : RowSquare [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,4,4,2] := by
  exact rowSquare_join (by decide) sg1762 sg4466

lemma sg14738 : RowSquare [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2889 sg2736

lemma sg14739 : RowSquare [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg2892 sg2726

lemma sg14740 : RowSquare [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2888 sg2737

lemma sg14741 : RowSquare [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg2726 sg2893

lemma sg14742 : RowSquare [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2889 sg2737

lemma sg14743 : RowSquare [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,4,4,2] := by
  exact rowSquare_join (by decide) sg2891 sg2737

lemma sg14744 : RowSquare [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,2] := by
  exact rowSquare_join (by decide) sg2278 sg3589

lemma sg14745 : RowSquare [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2892 sg2734

lemma sg14746 : RowSquare [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,1] := by
  exact rowSquare_join (by decide) sg2891 sg2738

lemma sg14747 : RowSquare [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,3,3,2] := by
  exact rowSquare_join (by decide) sg2891 sg2740

lemma sg14748 : RowSquare [6,6,2,2,2,2,2,2,2,1,1] [7,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg408 sg7813

lemma sg14749 : RowSquare [6,6,2,2,2,2,2,2,2,1,1] [7,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg409 sg7813

lemma sg14750 : RowSquare [6,6,2,2,2,2,2,2,2,1,1] [7,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg410 sg7813

lemma sg14751 : RowSquare [6,6,2,2,2,2,2,2,2,1,1] [7,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg7829

lemma sg14752 : RowSquare [6,6,2,2,2,2,2,2,2,1,1] [7,7,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg7830

lemma sg14753 : RowSquare [6,6,2,2,2,2,2,2,2,1,1] [8,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg411 sg7813

lemma sg14754 : RowSquare [6,6,2,2,2,2,2,2,2,1,1] [8,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg412 sg7813

lemma sg14755 : RowSquare [6,6,2,2,2,2,2,2,2,1,1] [8,7,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg7847

lemma sg14756 : RowSquare [6,6,3,2,1,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg1758 sg4438

lemma sg14757 : RowSquare [6,6,3,2,1,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,3] := by
  exact rowSquare_join (by decide) sg1332 sg4949

lemma sg14758 : RowSquare [6,6,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg1873 sg4379

lemma sg14759 : RowSquare [6,6,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,3] := by
  exact rowSquare_join (by decide) sg1332 sg4956

lemma sg14760 : RowSquare [6,6,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,4,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg3107 sg2633

lemma sg14761 : RowSquare [6,6,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,5,5,4,4,3] := by
  exact rowSquare_join (by decide) sg1873 sg4384

lemma sg14762 : RowSquare [6,6,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,4,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2633 sg3109

lemma sg14763 : RowSquare [6,6,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,3] := by
  exact rowSquare_join (by decide) sg2640 sg3108

lemma sg14764 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg3617

lemma sg14765 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg3620

lemma sg14766 : RowSquare [7,6,3,2,2,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1754 sg4163

lemma sg14767 : RowSquare [7,6,3,2,2,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2626 sg2707

lemma sg14768 : RowSquare [7,6,3,2,2,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1754 sg4164

lemma sg14769 : RowSquare [7,6,3,2,2,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2626 sg2708

lemma sg14770 : RowSquare [7,6,3,2,2,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg4167

lemma sg14771 : RowSquare [7,6,3,2,2,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2627 sg2703

lemma sg14772 : RowSquare [7,6,3,2,2,1,1,1,1,1,1,1,1] [6,5,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg2710 sg2640

lemma sg14773 : RowSquare [7,6,3,2,2,1,1,1,1,1,1,1,1] [6,6,4,4,4,4] := by
  exact rowSquare_join (by decide) sg74 sg11060

lemma sg14774 : RowSquare [7,6,3,2,2,1,1,1,1,1,1,1,1] [8,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg391 sg7997

lemma sg14775 : RowSquare [7,7,2,2,1,1,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2702 sg2702

lemma sg14776 : RowSquare [7,7,2,2,2,1,1,1,1,1,1,1,1] [6,6,6,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg3351

lemma sg14777 : RowSquare [7,7,3,2,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2251 sg3311

lemma sg14778 : RowSquare [7,7,3,2,1,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2251 sg3312

lemma sg14779 : RowSquare [7,7,3,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg3313

lemma sg14780 : RowSquare [7,7,3,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg3314

lemma sg14781 : RowSquare [8,7,1,1,1,1,1,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2251 sg3523

lemma sg14782 : RowSquare [8,7,2,2,1,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2705 sg2619

lemma sg14783 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2879 sg2546

lemma sg14784 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2073 sg3522

lemma sg14785 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2252 sg3259

lemma sg14786 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2074 sg3522

lemma sg14787 : RowSquare [8,8,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2115 sg3524

lemma sg14788 : RowSquare [8,8,2,2,2,2,2,2] [2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2566 sg2573

lemma sg14789 : RowSquare [8,8,2,2,2,2,2,2] [2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2566 sg2572

lemma sg14790 : RowSquare [8,8,2,2,2,2,2,2] [2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2566 sg2571

lemma sg14791 : RowSquare [8,8,2,2,2,2,2,2] [2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2566 sg2570

lemma sg14792 : RowSquare [8,8,2,2,2,2,2,2] [2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2566 sg2569

lemma sg14793 : RowSquare [8,8,2,2,2,2,2,2] [2,2,2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2566 sg2568

lemma sg14794 : RowSquare [8,8,2,2,2,2,2,2] [2,2,2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2566 sg2566

lemma sg14795 : RowSquare [8,8,2,2,2,2,2,2] [3,3,3,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2563 sg2563

lemma sg14796 : RowSquare [8,8,2,2,2,2,2,2] [4,4,4,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2562 sg2565

lemma sg14797 : RowSquare [8,8,2,2,2,2,2,2] [4,4,4,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2559 sg2567

lemma sg14798 : RowSquare [8,8,2,2,2,2,2,2] [4,4,4,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2562 sg2562

lemma sg14799 : RowSquare [8,8,2,2,2,2,2,2] [4,4,4,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg2559 sg2562

lemma sg14800 : RowSquare [8,8,2,2,2,2,2,2] [5,4,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2554 sg2562

lemma sg14801 : RowSquare [8,8,2,2,2,2,2,2] [5,4,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg2554 sg2559

lemma sg14802 : RowSquare [9,7,2,2,1,1,1,1,1,1,1,1] [4,4,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1147 sg4930

lemma sg14803 : RowSquare [9,7,2,2,1,1,1,1,1,1,1,1] [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg737 sg5757

lemma sg14804 : RowSquare [9,7,2,2,1,1,1,1,1,1,1,1] [5,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg739 sg5757

lemma sg14805 : RowSquare [9,7,2,2,1,1,1,1,1,1,1,1] [5,5,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg740 sg5757

lemma sg14806 : RowSquare [9,7,2,2,1,1,1,1,1,1,1,1] [5,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg741 sg5757

lemma sg14807 : RowSquare [9,7,2,2,1,1,1,1,1,1,1,1] [6,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg748 sg5757

lemma sg14808 : RowSquare [9,7,2,2,2,2,2,1,1] [2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2595 sg2527

lemma sg14809 : RowSquare [9,7,2,2,2,2,2,1,1] [2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2595 sg2526

lemma sg14810 : RowSquare [9,7,2,2,2,2,2,1,1] [2,2,2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2595 sg2525

lemma sg14811 : RowSquare [9,7,2,2,2,2,2,1,1] [2,2,2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2595 sg2524

lemma sg14812 : RowSquare [11,4,2,2,2,2,2,2,1] [6,6,6,5,5] := by
  exact rowSquare_join (by decide) sg879 sg5380

lemma sg14813 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1] [5,5,5,5,5,2,2] := by
  exact rowSquare_join (by decide) sg2925 sg3362

lemma sg14814 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1] [6,5,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg2759 sg3420

lemma sg14815 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1] [6,5,5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg2926 sg3362

lemma sg14816 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1] [6,6,6,6,5] := by
  exact rowSquare_join (by decide) sg1033 sg6490

lemma sg14817 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1] [7,5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg2929 sg3362

lemma sg14818 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1] [7,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg2930 sg3362

lemma sg14819 : RowSquare [5,4,3,3,2,2,2,2,2,2,1,1] [4,4,4,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2596 sg3520

lemma sg14820 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2137 sg4539

lemma sg14821 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg3505

lemma sg14822 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,2,2] := by
  exact rowSquare_join (by decide) sg1891 sg4923

lemma sg14823 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,3,1] := by
  exact rowSquare_join (by decide) sg1891 sg4924

lemma sg14824 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1736 sg4992

lemma sg14825 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2213 sg4442

lemma sg14826 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,3] := by
  exact rowSquare_join (by decide) sg1688 sg5005

lemma sg14827 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2663 sg3686

lemma sg14828 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2663 sg3688

lemma sg14829 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,4,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2902 sg3509

lemma sg14830 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2903 sg3506

lemma sg14831 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg3510

lemma sg14832 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2902 sg3511

lemma sg14833 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2903 sg3507

lemma sg14834 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2842 sg3563

lemma sg14835 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2903 sg3508

lemma sg14836 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2663 sg3693

lemma sg14837 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,4,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2903 sg3509

lemma sg14838 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,5,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2903 sg3511

lemma sg14839 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,5,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2663 sg3700

lemma sg14840 : RowSquare [5,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,4,3,2] := by
  exact rowSquare_join (by decide) sg2925 sg3475

lemma sg14841 : RowSquare [5,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,4,4,1] := by
  exact rowSquare_join (by decide) sg1688 sg5002

lemma sg14842 : RowSquare [5,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,2,2] := by
  exact rowSquare_join (by decide) sg2925 sg3476

lemma sg14843 : RowSquare [5,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,3,1] := by
  exact rowSquare_join (by decide) sg1688 sg5003

lemma sg14844 : RowSquare [5,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,4] := by
  exact rowSquare_join (by decide) sg1688 sg5004

lemma sg14845 : RowSquare [5,4,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg4410

lemma sg14846 : RowSquare [5,4,4,3,2,2,2,2,2,2,1] [5,5,5,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2107 sg4343

lemma sg14847 : RowSquare [5,4,4,3,2,2,2,2,2,2,1] [7,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1871 sg4804

lemma sg14848 : RowSquare [5,4,4,3,3,2,1,1,1,1,1,1,1,1] [5,5,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg3362

lemma sg14849 : RowSquare [5,5,3,2,2,2,2,2,2,2,1,1] [5,4,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1928 sg4832

lemma sg14850 : RowSquare [5,5,3,2,2,2,2,2,2,2,1,1] [5,5,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1929 sg4832

lemma sg14851 : RowSquare [5,5,3,2,2,2,2,2,2,2,1,1] [5,5,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1930 sg4832

lemma sg14852 : RowSquare [5,5,3,2,2,2,2,2,2,2,1,1] [5,5,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1931 sg4832

lemma sg14853 : RowSquare [5,5,3,2,2,2,2,2,2,2,1,1] [6,4,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1932 sg4832

lemma sg14854 : RowSquare [5,5,3,2,2,2,2,2,2,2,1,1] [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1933 sg4832

lemma sg14855 : RowSquare [5,5,3,2,2,2,2,2,2,2,1,1] [6,5,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1934 sg4832

lemma sg14856 : RowSquare [5,5,3,2,2,2,2,2,2,2,1,1] [6,6,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1935 sg4832

lemma sg14857 : RowSquare [5,5,3,2,2,2,2,2,2,2,1,1] [6,6,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1936 sg4832

lemma sg14858 : RowSquare [5,5,3,2,2,2,2,2,2,2,1,1] [7,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1937 sg4832

lemma sg14859 : RowSquare [5,5,3,2,2,2,2,2,2,2,1,1] [7,4,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1938 sg4832

lemma sg14860 : RowSquare [5,5,3,2,2,2,2,2,2,2,1,1] [7,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1939 sg4832

lemma sg14861 : RowSquare [5,5,3,2,2,2,2,2,2,2,1,1] [7,5,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1940 sg4832

lemma sg14862 : RowSquare [5,5,3,2,2,2,2,2,2,2,1,1] [7,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1941 sg4832

lemma sg14863 : RowSquare [5,5,3,2,2,2,2,2,2,2,1,1] [7,6,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1942 sg4832

lemma sg14864 : RowSquare [5,5,3,2,2,2,2,2,2,2,1,1] [7,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1943 sg4832

lemma sg14865 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2746 sg3614

lemma sg14866 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,4,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1875 sg4919

lemma sg14867 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,4,4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2750 sg3614

lemma sg14868 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,4,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1876 sg4920

lemma sg14869 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2902 sg3477

lemma sg14870 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg3478

lemma sg14871 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg2904 sg3470

lemma sg14872 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2752 sg3614

lemma sg14873 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg2743 sg3615

lemma sg14874 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2753 sg3614

lemma sg14875 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1499 sg5754

lemma sg14876 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2902 sg3479

lemma sg14877 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1874 sg4925

lemma sg14878 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2371 sg4317

lemma sg14879 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2741 sg3616

lemma sg14880 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2903 sg3472

lemma sg14881 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg3480

lemma sg14882 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg2904 sg3471

lemma sg14883 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg3481

lemma sg14884 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg2904 sg3472

lemma sg14885 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2746 sg3615

lemma sg14886 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg2743 sg3617

lemma sg14887 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2957 sg3409

lemma sg14888 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2743 sg3618

lemma sg14889 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1876 sg4921

lemma sg14890 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2372 sg4317

lemma sg14891 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2903 sg3474

lemma sg14892 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg3482

lemma sg14893 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg2904 sg3473

lemma sg14894 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg2904 sg3474

lemma sg14895 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,3,2] := by
  exact rowSquare_join (by decide) sg2743 sg3619

lemma sg14896 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,4,1] := by
  exact rowSquare_join (by decide) sg2743 sg3620

lemma sg14897 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,4] := by
  exact rowSquare_join (by decide) sg2167 sg4488

lemma sg14898 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg2904 sg3476

lemma sg14899 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg2743 sg3622

lemma sg14900 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,3] := by
  exact rowSquare_join (by decide) sg2167 sg4489

lemma sg14901 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2291 sg4403

lemma sg14902 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg998 sg6501

lemma sg14903 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2744 sg3616

lemma sg14904 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2905 sg3472

lemma sg14905 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2746 sg3616

lemma sg14906 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg3483

lemma sg14907 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2958 sg3409

lemma sg14908 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg3484

lemma sg14909 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2140 sg4533

lemma sg14910 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2905 sg3474

lemma sg14911 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2371 sg4318

lemma sg14912 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg975 sg6508

lemma sg14913 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg3485

lemma sg14914 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg2907 sg3471

lemma sg14915 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg2906 sg3473

lemma sg14916 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg2906 sg3474

lemma sg14917 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,4] := by
  exact rowSquare_join (by decide) sg2746 sg3620

lemma sg14918 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg2906 sg3476

lemma sg14919 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,2] := by
  exact rowSquare_join (by decide) sg2746 sg3622

lemma sg14920 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg3486

lemma sg14921 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2140 sg4534

lemma sg14922 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1878 sg4921

lemma sg14923 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2141 sg4534

lemma sg14924 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2140 sg4535

lemma sg14925 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,2,1] := by
  exact rowSquare_join (by decide) sg2907 sg3473

lemma sg14926 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,3] := by
  exact rowSquare_join (by decide) sg2907 sg3474

lemma sg14927 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,5,1] := by
  exact rowSquare_join (by decide) sg2907 sg3476

lemma sg14928 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,3,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1880 sg4919

lemma sg14929 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2757 sg3614

lemma sg14930 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1945 sg4889

lemma sg14931 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2902 sg3487

lemma sg14932 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2369 sg4322

lemma sg14933 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2376 sg4317

lemma sg14934 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg3488

lemma sg14935 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg3489

lemma sg14936 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2752 sg3615

lemma sg14937 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2902 sg3490

lemma sg14938 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2370 sg4322

lemma sg14939 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2958 sg3412

end UniversalTensorSquare
end
end

end OAI
