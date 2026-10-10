import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes37

namespace OAI

/-! Semigroup Nodes 50. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20540 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [6,3,3,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg14770

lemma sg20541 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [6,5,5,5,5,4,1] := by
  exact rowSquare_join (by decide) sg2710 sg4842

lemma sg20542 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [6,6,5,5,4,4,1] := by
  exact rowSquare_join (by decide) sg74 sg12703

lemma sg20543 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [6,6,5,5,5,2,2] := by
  exact rowSquare_join (by decide) sg2712 sg4841

lemma sg20544 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [6,6,5,5,5,3,1] := by
  exact rowSquare_join (by decide) sg2712 sg4842

lemma sg20545 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [6,6,5,5,5,4] := by
  exact rowSquare_join (by decide) sg74 sg12704

lemma sg20546 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [6,6,6,4,4,4,1] := by
  exact rowSquare_join (by decide) sg74 sg12705

lemma sg20547 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [6,6,6,5,4,4] := by
  exact rowSquare_join (by decide) sg74 sg12706

lemma sg20548 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [6,6,6,6,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14549

lemma sg20549 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [6,6,6,6,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14458

lemma sg20550 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [7,5,5,5,5,4] := by
  exact rowSquare_join (by decide) sg74 sg12708

lemma sg20551 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [7,6,5,4,4,4,1] := by
  exact rowSquare_join (by decide) sg4 sg14772

lemma sg20552 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [7,6,5,5,4,4] := by
  exact rowSquare_join (by decide) sg0 sg15649

lemma sg20553 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [7,6,6,4,4,4] := by
  exact rowSquare_join (by decide) sg0 sg15650

lemma sg20554 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [7,6,6,6,6] := by
  exact rowSquare_join (by decide) sg841 sg8174

lemma sg20555 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [7,7,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg74 sg12709

lemma sg20556 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [7,7,5,4,4,4] := by
  exact rowSquare_join (by decide) sg4 sg14773

lemma sg20557 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [7,7,6,6,5] := by
  exact rowSquare_join (by decide) sg194 sg11730

lemma sg20558 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [7,7,7,5,5] := by
  exact rowSquare_join (by decide) sg982 sg8076

lemma sg20559 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [7,7,7,7,1,1,1] := by
  exact rowSquare_join (by decide) sg390 sg11535

lemma sg20560 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [7,7,7,7,2,1] := by
  exact rowSquare_join (by decide) sg644 sg8921

lemma sg20561 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [7,7,7,7,3] := by
  exact rowSquare_join (by decide) sg644 sg8922

lemma sg20562 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [8,7,7,7,1,1] := by
  exact rowSquare_join (by decide) sg981 sg8086

lemma sg20563 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [8,7,7,7,2] := by
  exact rowSquare_join (by decide) sg982 sg8086

lemma sg20564 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [8,8,7,7,1] := by
  exact rowSquare_join (by decide) sg644 sg8933

lemma sg20565 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [8,8,8,6,1] := by
  exact rowSquare_join (by decide) sg1075 sg8075

lemma sg20566 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [8,8,8,7] := by
  exact rowSquare_join (by decide) sg364 sg11166

lemma sg20567 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [9,3,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg842 sg8175

lemma sg20568 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [9,4,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg838 sg8178

lemma sg20569 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [9,4,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg842 sg8176

lemma sg20570 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [9,4,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg15 sg14457

lemma sg20571 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [9,5,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1224 sg6709

lemma sg20572 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [9,5,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg1688 sg5822

lemma sg20573 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [9,5,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1275 sg6561

lemma sg20574 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [9,5,5,4,4,4] := by
  exact rowSquare_join (by decide) sg4 sg14774

lemma sg20575 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [9,5,5,5,4,3] := by
  exact rowSquare_join (by decide) sg791 sg8408

lemma sg20576 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [9,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg792 sg8408

lemma sg20577 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [9,6,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1274 sg6562

lemma sg20578 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [9,6,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1275 sg6562

lemma sg20579 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [9,6,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1688 sg5825

lemma sg20580 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [9,6,5,4,4,3] := by
  exact rowSquare_join (by decide) sg1688 sg5826

lemma sg20581 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [9,7,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg843 sg8177

lemma sg20582 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [9,7,4,4,4,3] := by
  exact rowSquare_join (by decide) sg794 sg8407

lemma sg20583 : RowSquare [9,7,4,3,2,2,2,1,1] [8,8,7,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3514 sg3739

lemma sg20584 : RowSquare [9,7,4,3,2,2,2,1,1] [8,8,8,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3241 sg3950

lemma sg20585 : RowSquare [9,7,4,3,2,2,2,1,1] [9,7,7,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3513 sg3740

lemma sg20586 : RowSquare [9,7,4,3,2,2,2,1,1] [9,8,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3513 sg3743

lemma sg20587 : RowSquare [9,7,4,3,2,2,2,1,1] [9,8,7,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3514 sg3740

lemma sg20588 : RowSquare [9,7,4,3,2,2,2,1,1] [9,9,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3240 sg3955

lemma sg20589 : RowSquare [9,7,4,3,2,2,2,1,1] [9,9,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3272 sg3917

lemma sg20590 : RowSquare [9,7,4,3,2,2,2,1,1] [9,9,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3206 sg3970

lemma sg20591 : RowSquare [9,7,4,3,2,2,2,1,1] [9,9,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3206 sg3971

lemma sg20592 : RowSquare [9,7,4,3,2,2,2,1,1] [9,9,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3514 sg3741

lemma sg20593 : RowSquare [9,7,4,3,2,2,2,1,1] [9,9,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3514 sg3742

lemma sg20594 : RowSquare [9,7,4,3,2,2,2,1,1] [9,9,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3514 sg3743

lemma sg20595 : RowSquare [9,7,4,3,2,2,2,1,1] [10,3,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3242 sg3954

lemma sg20596 : RowSquare [9,7,4,3,2,2,2,1,1] [10,3,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3206 sg3972

lemma sg20597 : RowSquare [9,7,4,3,2,2,2,1,1] [10,3,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3297 sg3849

lemma sg20598 : RowSquare [9,7,4,3,2,2,2,1,1] [10,3,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3273 sg3915

lemma sg20599 : RowSquare [9,7,4,3,2,2,2,1,1] [10,4,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3293 sg3852

lemma sg20600 : RowSquare [9,7,4,3,2,2,2,1,1] [10,4,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3207 sg3969

lemma sg20601 : RowSquare [9,7,4,3,2,2,2,1,1] [10,4,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3206 sg3973

lemma sg20602 : RowSquare [9,7,4,3,2,2,2,1,1] [10,4,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3296 sg3851

lemma sg20603 : RowSquare [9,7,4,3,2,2,2,1,1] [10,4,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3293 sg3853

lemma sg20604 : RowSquare [9,7,4,3,2,2,2,1,1] [10,4,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3271 sg3918

lemma sg20605 : RowSquare [9,7,4,3,2,2,2,1,1] [10,4,4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3206 sg3974

lemma sg20606 : RowSquare [9,7,4,3,2,2,2,1,1] [10,4,4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3293 sg3854

lemma sg20607 : RowSquare [9,7,4,3,2,2,2,1,1] [10,4,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3271 sg3919

lemma sg20608 : RowSquare [9,7,4,3,2,2,2,1,1] [10,4,4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3206 sg3975

lemma sg20609 : RowSquare [9,7,4,3,2,2,2,1,1] [10,4,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3206 sg3976

lemma sg20610 : RowSquare [9,7,4,3,2,2,2,1,1] [10,5,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3295 sg3852

lemma sg20611 : RowSquare [9,7,4,3,2,2,2,1,1] [10,5,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3208 sg3969

lemma sg20612 : RowSquare [9,7,4,3,2,2,2,1,1] [10,5,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3271 sg3920

lemma sg20613 : RowSquare [9,7,4,3,2,2,2,1,1] [10,5,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3206 sg3977

lemma sg20614 : RowSquare [9,7,4,3,2,2,2,1,1] [10,5,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3295 sg3854

lemma sg20615 : RowSquare [9,7,4,3,2,2,2,1,1] [10,5,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3272 sg3918

lemma sg20616 : RowSquare [9,7,4,3,2,2,2,1,1] [10,5,4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3271 sg3921

lemma sg20617 : RowSquare [9,7,4,3,2,2,2,1,1] [10,5,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3206 sg3978

lemma sg20618 : RowSquare [9,7,4,3,2,2,2,1,1] [10,5,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3271 sg3922

lemma sg20619 : RowSquare [9,7,4,3,2,2,2,1,1] [10,5,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3206 sg3979

lemma sg20620 : RowSquare [9,7,4,3,2,2,2,1,1] [10,5,5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3293 sg3856

lemma sg20621 : RowSquare [9,7,4,3,2,2,2,1,1] [10,5,5,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3271 sg3923

lemma sg20622 : RowSquare [9,7,4,3,2,2,2,1,1] [10,5,5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3206 sg3980

lemma sg20623 : RowSquare [9,7,4,3,2,2,2,1,1] [10,6,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3295 sg3855

lemma sg20624 : RowSquare [9,7,4,3,2,2,2,1,1] [10,6,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3272 sg3920

lemma sg20625 : RowSquare [9,7,4,3,2,2,2,1,1] [10,6,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3271 sg3925

lemma sg20626 : RowSquare [9,7,4,3,2,2,2,1,1] [10,6,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3206 sg3981

lemma sg20627 : RowSquare [9,7,4,3,2,2,2,1,1] [10,6,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3272 sg3921

lemma sg20628 : RowSquare [9,7,4,3,2,2,2,1,1] [10,6,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3271 sg3926

lemma sg20629 : RowSquare [9,7,4,3,2,2,2,1,1] [10,7,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3295 sg3857

lemma sg20630 : RowSquare [9,7,4,3,2,2,2,1,1] [10,7,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3272 sg3925

lemma sg20631 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3375 sg4023

lemma sg20632 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3522 sg3964

lemma sg20633 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3523 sg3964

lemma sg20634 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2546 sg4931

lemma sg20635 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3524 sg3964

lemma sg20636 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2546 sg4933

lemma sg20637 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3522 sg3966

lemma sg20638 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3526 sg3964

lemma sg20639 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [5,4,3,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3522 sg3967

lemma sg20640 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [5,4,3,3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3523 sg3966

lemma sg20641 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [5,4,3,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3527 sg3964

lemma sg20642 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [5,4,4,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2699 sg4847

lemma sg20643 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [5,4,4,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3524 sg3966

lemma sg20644 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2699 sg4848

lemma sg20645 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3523 sg3967

lemma sg20646 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [5,5,4,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3524 sg3967

lemma sg20647 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3256 sg4348

lemma sg20648 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2040 sg5760

lemma sg20649 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3258 sg4346

lemma sg20650 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2548 sg4933

lemma sg20651 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [5,5,5,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3309 sg4155

lemma sg20652 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2044 sg5758

lemma sg20653 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3258 sg4348

lemma sg20654 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [6,3,3,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15657

lemma sg20655 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [6,3,3,3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3526 sg3966

lemma sg20656 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [6,3,3,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3529 sg3964

lemma sg20657 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [6,6,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3256 sg4352

lemma sg20658 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [6,6,4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3258 sg4352

lemma sg20659 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [7,3,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15250

lemma sg20660 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [7,6,6,6,6] := by
  exact rowSquare_join (by decide) sg841 sg8213

lemma sg20661 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [7,7,6,6,5] := by
  exact rowSquare_join (by decide) sg13 sg14548

lemma sg20662 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [7,7,7,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14776

lemma sg20663 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [7,7,7,5,5] := by
  exact rowSquare_join (by decide) sg4 sg14812

lemma sg20664 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [7,7,7,7,2,1] := by
  exact rowSquare_join (by decide) sg364 sg11186

lemma sg20665 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [7,7,7,7,3] := by
  exact rowSquare_join (by decide) sg364 sg11187

lemma sg20666 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [8,7,7,7,1,1] := by
  exact rowSquare_join (by decide) sg656 sg8921

lemma sg20667 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [8,7,7,7,2] := by
  exact rowSquare_join (by decide) sg656 sg8922

lemma sg20668 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [8,8,7,7,1] := by
  exact rowSquare_join (by decide) sg364 sg11198

lemma sg20669 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [8,8,8,6,1] := by
  exact rowSquare_join (by decide) sg364 sg11200

lemma sg20670 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [8,8,8,7] := by
  exact rowSquare_join (by decide) sg364 sg11201

lemma sg20671 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [9,3,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg842 sg8214

lemma sg20672 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [9,4,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg838 sg8216

lemma sg20673 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [9,4,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg842 sg8215

lemma sg20674 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [9,5,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg838 sg8217

lemma sg20675 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [9,5,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1235 sg6711

lemma sg20676 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [9,5,5,5,4,3] := by
  exact rowSquare_join (by decide) sg497 sg9653

lemma sg20677 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [9,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg497 sg9654

lemma sg20678 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [9,6,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg838 sg8218

lemma sg20679 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [9,6,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg839 sg8218

lemma sg20680 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [9,6,5,4,4,3] := by
  exact rowSquare_join (by decide) sg489 sg9656

lemma sg20681 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [9,7,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15659

lemma sg20682 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [9,7,4,4,4,3] := by
  exact rowSquare_join (by decide) sg491 sg9655

lemma sg20683 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14459

lemma sg20684 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg14777

lemma sg20685 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14460

lemma sg20686 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2699 sg4834

lemma sg20687 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg12598

lemma sg20688 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg14 sg14459

lemma sg20689 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14461

lemma sg20690 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14462

lemma sg20691 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14463

lemma sg20692 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg123 sg11748

lemma sg20693 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14464

lemma sg20694 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14465

lemma sg20695 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14466

lemma sg20696 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14467

lemma sg20697 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14468

lemma sg20698 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14469

lemma sg20699 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14470

lemma sg20700 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14471

lemma sg20701 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg14777

lemma sg20702 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg14778

lemma sg20703 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15660

lemma sg20704 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg75 sg12598

lemma sg20705 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15661

lemma sg20706 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2699 sg4836

lemma sg20707 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg142 sg11738

lemma sg20708 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg14460

lemma sg20709 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3522 sg3948

lemma sg20710 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3522 sg3949

lemma sg20711 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15662

lemma sg20712 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg12599

lemma sg20713 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3522 sg3951

lemma sg20714 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14779

lemma sg20715 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg165 sg11733

lemma sg20716 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14780

lemma sg20717 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14472

lemma sg20718 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14473

lemma sg20719 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3522 sg3952

lemma sg20720 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14474

lemma sg20721 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2699 sg4841

lemma sg20722 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2701 sg4834

lemma sg20723 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14461

lemma sg20724 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg14 sg14462

lemma sg20725 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,3,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14475

lemma sg20726 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,3,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14476

lemma sg20727 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,3,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14477

lemma sg20728 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14467

lemma sg20729 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,3,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14468

lemma sg20730 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14470

lemma sg20731 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14471

lemma sg20732 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,4,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg55 sg12638

lemma sg20733 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,4,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg123 sg11751

lemma sg20734 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,4,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg27 sg12925

lemma sg20735 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,4,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2529 sg4931

lemma sg20736 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14478

lemma sg20737 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14479

lemma sg20738 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14480

lemma sg20739 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14481

lemma sg20740 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14482

lemma sg20741 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2528 sg4933

lemma sg20742 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2529 sg4933

lemma sg20743 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg55 sg12639

lemma sg20744 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg55 sg12640

lemma sg20745 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg55 sg12641

lemma sg20746 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg55 sg12642

lemma sg20747 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg123 sg11753

lemma sg20748 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg167 sg11733

lemma sg20749 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg12600

lemma sg20750 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14483

lemma sg20751 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14484

lemma sg20752 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2530 sg4933

lemma sg20753 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg12601

lemma sg20754 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg12602

lemma sg20755 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14485

lemma sg20756 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14486

lemma sg20757 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14487

lemma sg20758 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14488

lemma sg20759 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2531 sg4933

lemma sg20760 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg15 sg14459

lemma sg20761 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15663

lemma sg20762 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15251

lemma sg20763 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [6,4,3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15664

lemma sg20764 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [6,4,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg14780

lemma sg20765 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [6,6,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14475

lemma sg20766 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [6,6,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14476

lemma sg20767 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [6,6,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg14 sg14477

lemma sg20768 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2533 sg4933

lemma sg20769 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [7,3,3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15252

lemma sg20770 : RowSquare [9,8,3,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3292 sg3934

lemma sg20771 : RowSquare [9,8,3,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3292 sg3932

lemma sg20772 : RowSquare [9,8,3,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3292 sg3931

lemma sg20773 : RowSquare [9,8,3,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3292 sg3930

lemma sg20774 : RowSquare [9,8,3,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3292 sg3928

lemma sg20775 : RowSquare [9,8,3,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3292 sg3927

lemma sg20776 : RowSquare [9,8,3,2,2,2,2,2,1] [3,3,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3291 sg3933

lemma sg20777 : RowSquare [9,8,3,2,2,2,2,2,1] [3,3,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3291 sg3932

lemma sg20778 : RowSquare [9,8,3,2,2,2,2,2,1] [3,3,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3291 sg3931

lemma sg20779 : RowSquare [9,8,3,2,2,2,2,2,1] [3,3,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3291 sg3930

lemma sg20780 : RowSquare [9,8,3,2,2,2,2,2,1] [3,3,2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3291 sg3928

lemma sg20781 : RowSquare [9,8,3,2,2,2,2,2,1] [3,3,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3291 sg3927

lemma sg20782 : RowSquare [9,8,3,2,2,2,2,2,1] [4,4,4,4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3288 sg3929

lemma sg20783 : RowSquare [9,8,3,2,2,2,2,2,1] [4,4,4,4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3290 sg3924

lemma sg20784 : RowSquare [9,8,3,2,2,2,2,2,1] [5,5,5,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg2557 sg4783

lemma sg20785 : RowSquare [9,8,3,2,2,2,2,2,1] [5,5,5,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3196 sg3997

lemma sg20786 : RowSquare [9,8,3,2,2,2,2,2,1] [5,5,5,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg3196 sg3996

lemma sg20787 : RowSquare [9,8,3,2,2,2,2,2,1] [5,5,5,5,5,4,2] := by
  exact rowSquare_join (by decide) sg1324 sg6555

lemma sg20788 : RowSquare [9,8,3,2,2,2,2,2,1] [5,5,5,5,5,5,1] := by
  exact rowSquare_join (by decide) sg982 sg8115

lemma sg20789 : RowSquare [9,9,2,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14490

lemma sg20790 : RowSquare [9,9,2,2,1,1,1,1,1,1,1,1,1] [5,5,4,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14491

lemma sg20791 : RowSquare [9,9,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14492

lemma sg20792 : RowSquare [10,8,1,1,1,1,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg14781

lemma sg20793 : RowSquare [10,8,1,1,1,1,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg17 sg14489

lemma sg20794 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg142 sg11748

lemma sg20795 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg143 sg11748

lemma sg20796 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg144 sg11748

lemma sg20797 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg145 sg11748

lemma sg20798 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg142 sg11749

lemma sg20799 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg142 sg11750

lemma sg20800 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg146 sg11748

lemma sg20801 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg143 sg11749

lemma sg20802 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg143 sg11750

lemma sg20803 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg295 sg11425

lemma sg20804 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg147 sg11748

lemma sg20805 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg144 sg11749

lemma sg20806 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg144 sg11750

lemma sg20807 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg142 sg11753

lemma sg20808 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12924

lemma sg20809 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg297 sg11425

lemma sg20810 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12925

lemma sg20811 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12926

lemma sg20812 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg142 sg11754

lemma sg20813 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12927

lemma sg20814 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg148 sg11748

lemma sg20815 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,5,3,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg143 sg11751

lemma sg20816 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,5,3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg295 sg11426

lemma sg20817 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,5,4,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg12922

lemma sg20818 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,5,4,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg40 sg12923

lemma sg20819 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,5,4,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg295 sg11427

lemma sg20820 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,5,4,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg12927

lemma sg20821 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg295 sg11428

lemma sg20822 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg295 sg11429

lemma sg20823 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg14782

lemma sg20824 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg11733

lemma sg20825 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg297 sg11427

lemma sg20826 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg296 sg11428

lemma sg20827 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg296 sg11429

lemma sg20828 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg297 sg11428

lemma sg20829 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg297 sg11429

lemma sg20830 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [6,3,3,3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg149 sg11748

lemma sg20831 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg15256

lemma sg20832 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg145 sg11749

lemma sg20833 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg298 sg11425

lemma sg20834 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg142 sg11756

lemma sg20835 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [6,4,3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg150 sg11748

lemma sg20836 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [6,4,3,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg146 sg11749

lemma sg20837 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [6,4,3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15680

lemma sg20838 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [6,4,3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg295 sg11430

lemma sg20839 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [6,4,4,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg147 sg11749

lemma sg20840 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [6,5,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg151 sg11748

lemma sg20841 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [6,5,3,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg148 sg11749

lemma sg20842 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [6,5,3,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg148 sg11750

lemma sg20843 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [6,6,3,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg148 sg11751

lemma sg20844 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12607

lemma sg20845 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12608

lemma sg20846 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg12600

lemma sg20847 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11237

lemma sg20848 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [7,3,3,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12606

lemma sg20849 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [7,4,3,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg57 sg12679

lemma sg20850 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [7,5,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg12928

lemma sg20851 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg165 sg11748

lemma sg20852 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11748

lemma sg20853 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12635

lemma sg20854 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg83 sg12636

lemma sg20855 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg167 sg11748

lemma sg20856 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12635

lemma sg20857 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg84 sg12636

lemma sg20858 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg168 sg11748

lemma sg20859 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg165 sg11749

lemma sg20860 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg165 sg11750

lemma sg20861 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg12933

lemma sg20862 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg40 sg12934

lemma sg20863 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg169 sg11748

lemma sg20864 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11749

lemma sg20865 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg166 sg11750

lemma sg20866 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg165 sg11751

lemma sg20867 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg170 sg11748

lemma sg20868 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,4,4,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14525

lemma sg20869 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,4,4,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg167 sg11749

lemma sg20870 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,4,4,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg165 sg11753

lemma sg20871 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg358 sg11255

lemma sg20872 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg165 sg11754

lemma sg20873 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg171 sg11748

lemma sg20874 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,5,3,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11751

lemma sg20875 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,5,4,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12637

lemma sg20876 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,5,4,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12638

lemma sg20877 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,5,4,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg167 sg11752

lemma sg20878 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12639

lemma sg20879 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12640

lemma sg20880 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12641

lemma sg20881 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12643

lemma sg20882 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12644

lemma sg20883 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12645

lemma sg20884 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12646

lemma sg20885 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg41 sg12934

lemma sg20886 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg172 sg11748

lemma sg20887 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg168 sg11749

lemma sg20888 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg168 sg11750

lemma sg20889 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg85 sg12636

lemma sg20890 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [6,5,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg174 sg11748

lemma sg20891 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12647

lemma sg20892 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14787

lemma sg20893 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg12933

lemma sg20894 : RowSquare [5,5,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3408 sg4898

lemma sg20895 : RowSquare [5,5,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1682 sg8014

lemma sg20896 : RowSquare [5,5,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,4,4] := by
  exact rowSquare_join (by decide) sg1688 sg8012

lemma sg20897 : RowSquare [5,5,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,6,2] := by
  exact rowSquare_join (by decide) sg1688 sg8013

lemma sg20898 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3691 sg4865

lemma sg20899 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2626 sg5767

lemma sg20900 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3691 sg4866

lemma sg20901 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3691 sg4867

lemma sg20902 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3688 sg4870

lemma sg20903 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2632 sg5766

lemma sg20904 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,4,4] := by
  exact rowSquare_join (by decide) sg1688 sg8011

lemma sg20905 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,6,1,1] := by
  exact rowSquare_join (by decide) sg3691 sg4871

lemma sg20906 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4319 sg4358

lemma sg20907 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,4,4] := by
  exact rowSquare_join (by decide) sg4488 sg4035

lemma sg20908 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,3,3] := by
  exact rowSquare_join (by decide) sg4488 sg4036

lemma sg20909 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,7,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3963 sg4539

lemma sg20910 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,7,2,2] := by
  exact rowSquare_join (by decide) sg4378 sg4226

lemma sg20911 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,8,7,1] := by
  exact rowSquare_join (by decide) sg270 sg11554

lemma sg20912 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,8,8] := by
  exact rowSquare_join (by decide) sg271 sg11554

lemma sg20913 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [9,8,7,7,1] := by
  exact rowSquare_join (by decide) sg273 sg11554

lemma sg20914 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [9,8,8,6,1] := by
  exact rowSquare_join (by decide) sg476 sg11061

lemma sg20915 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [9,8,8,7] := by
  exact rowSquare_join (by decide) sg271 sg11568

lemma sg20916 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [10,7,7,7,1] := by
  exact rowSquare_join (by decide) sg476 sg11066

lemma sg20917 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [10,8,7,6,1] := by
  exact rowSquare_join (by decide) sg476 sg11074

lemma sg20918 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [10,8,7,7] := by
  exact rowSquare_join (by decide) sg456 sg11096

lemma sg20919 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [10,8,8,5,1] := by
  exact rowSquare_join (by decide) sg476 sg11075

lemma sg20920 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [10,8,8,6] := by
  exact rowSquare_join (by decide) sg477 sg11061

lemma sg20921 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [10,9,6,6,1] := by
  exact rowSquare_join (by decide) sg476 sg11079

lemma sg20922 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [10,10,6,5,1] := by
  exact rowSquare_join (by decide) sg476 sg11084

lemma sg20923 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [10,10,6,6] := by
  exact rowSquare_join (by decide) sg271 sg11583

lemma sg20924 : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [11,8,6,6,1] := by
  exact rowSquare_join (by decide) sg751 sg8895

lemma sg20925 : RowSquare [6,6,3,3,2,2,2,2,2,2,1,1] [4,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1461 sg8780

lemma sg20926 : RowSquare [6,6,3,3,2,2,2,2,2,2,1,1] [4,3,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1845 sg7812

lemma sg20927 : RowSquare [6,6,3,3,2,2,2,2,2,2,1,1] [4,3,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1844 sg7813

lemma sg20928 : RowSquare [6,6,3,3,2,2,2,2,2,2,1,1] [4,4,4,4,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1844 sg7817

lemma sg20929 : RowSquare [6,6,3,3,2,2,2,2,2,2,1,1] [4,4,4,4,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1844 sg7821

lemma sg20930 : RowSquare [6,6,3,3,2,2,2,2,2,2,1,1] [5,3,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1845 sg7813

lemma sg20931 : RowSquare [6,6,3,3,2,2,2,2,2,2,1,1] [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1468 sg8780

lemma sg20932 : RowSquare [6,6,3,3,2,2,2,2,2,2,1,1] [5,5,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1847 sg7814

lemma sg20933 : RowSquare [6,6,3,3,2,2,2,2,2,2,1,1] [5,5,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1469 sg8780

lemma sg20934 : RowSquare [6,6,3,3,2,2,2,2,2,2,1,1] [5,5,5,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1844 sg7838

lemma sg20935 : RowSquare [6,6,3,3,2,2,2,2,2,2,1,1] [6,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1470 sg8780

lemma sg20936 : RowSquare [6,6,3,3,2,2,2,2,2,2,1,1] [6,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1471 sg8780

lemma sg20937 : RowSquare [6,6,3,3,2,2,2,2,2,2,1,1] [6,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1472 sg8780

lemma sg20938 : RowSquare [6,6,3,3,2,2,2,2,2,2,1,1] [6,6,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1473 sg8780

lemma sg20939 : RowSquare [6,6,3,3,2,2,2,2,2,2,1,1] [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1468 sg8781

end UniversalTensorSquare
end
end

end OAI
