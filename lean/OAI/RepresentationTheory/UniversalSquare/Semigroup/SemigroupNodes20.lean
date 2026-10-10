import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes18
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes15
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes16

namespace OAI

/-! Semigroup Nodes 20. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8537 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1005 sg1327

lemma sg8538 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg1328

lemma sg8539 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1331

lemma sg8540 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1001 sg1328

lemma sg8541 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1332

lemma sg8542 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1006 sg1327

lemma sg8543 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg998 sg1329

lemma sg8544 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1007 sg1327

lemma sg8545 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1329

lemma sg8546 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg998 sg1330

lemma sg8547 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1008 sg1327

lemma sg8548 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg1329

lemma sg8549 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg998 sg1331

lemma sg8550 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1332

lemma sg8551 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg999 sg1330

lemma sg8552 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg1330

lemma sg8553 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg999 sg1331

lemma sg8554 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1001 sg1330

lemma sg8555 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg999 sg1332

lemma sg8556 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1000 sg1331

lemma sg8557 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1001 sg1331

lemma sg8558 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg1000 sg1332

lemma sg8559 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg1001 sg1332

lemma sg8560 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1009 sg1327

lemma sg8561 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1002 sg1328

lemma sg8562 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg6905

lemma sg8563 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1003 sg1328

lemma sg8564 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg6906

lemma sg8565 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1004 sg1328

lemma sg8566 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6907

lemma sg8567 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1002 sg1330

lemma sg8568 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1005 sg1328

lemma sg8569 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1002 sg1331

lemma sg8570 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1002 sg1332

lemma sg8571 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1338

lemma sg8572 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg6910

lemma sg8573 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1008 sg1328

lemma sg8574 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1003 sg1331

lemma sg8575 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1003 sg1332

lemma sg8576 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1004 sg1330

lemma sg8577 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1005 sg1330

lemma sg8578 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg1004 sg1332

lemma sg8579 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1005 sg1331

lemma sg8580 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg0 sg6917

lemma sg8581 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg0 sg6918

lemma sg8582 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg0 sg6919

lemma sg8583 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,5,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1015 sg1327

lemma sg8584 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1006 sg1329

lemma sg8585 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg998 sg1338

lemma sg8586 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,5,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1016 sg1327

lemma sg8587 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1007 sg1329

lemma sg8588 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1339

lemma sg8589 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg999 sg1338

lemma sg8590 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1008 sg1329

lemma sg8591 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1340

lemma sg8592 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1000 sg1338

lemma sg8593 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1001 sg1338

lemma sg8594 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1006 sg1332

lemma sg8595 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1008 sg1330

lemma sg8596 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg1000 sg1339

lemma sg8597 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1008 sg1331

lemma sg8598 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1000 sg1340

lemma sg8599 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,5,4,4,3] := by
  exact rowSquare_join (by decide) sg1001 sg1340

lemma sg8600 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1009 sg1328

lemma sg8601 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [6,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1012 sg1330

lemma sg8602 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [6,6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1006 sg1338

lemma sg8603 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [6,6,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1016 sg1329

lemma sg8604 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [6,6,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1006 sg1339

lemma sg8605 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [6,6,3,3,3] := by
  exact rowSquare_join (by decide) sg1001 sg1348

lemma sg8606 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,1] := by
  exact rowSquare_join (by decide) sg1008 sg1340

lemma sg8607 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [7,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1022 sg1328

lemma sg8608 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [7,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1023 sg1328

lemma sg8609 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [7,6,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1003 sg1348

lemma sg8610 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [7,6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg6995

lemma sg8611 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [7,7,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1023 sg1329

lemma sg8612 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [7,7,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1015 sg1338

lemma sg8613 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [7,7,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1006 sg1348

lemma sg8614 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [7,7,3,3,1] := by
  exact rowSquare_join (by decide) sg1008 sg1348

lemma sg8615 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg910 sg1327

lemma sg8616 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1754

lemma sg8617 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg589 sg1754

lemma sg8618 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg590 sg1754

lemma sg8619 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg914 sg1327

lemma sg8620 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg591 sg1754

lemma sg8621 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg592 sg1754

lemma sg8622 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [4,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg593 sg1754

lemma sg8623 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg594 sg1754

lemma sg8624 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [4,4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg595 sg1754

lemma sg8625 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [4,4,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg596 sg1754

lemma sg8626 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg915 sg1332

lemma sg8627 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg597 sg1754

lemma sg8628 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [5,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg598 sg1754

lemma sg8629 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [5,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg599 sg1754

lemma sg8630 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [5,4,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg600 sg1754

lemma sg8631 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [5,4,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg601 sg1754

lemma sg8632 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [5,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg930 sg1327

lemma sg8633 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [5,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg923 sg1328

lemma sg8634 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [5,5,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg602 sg1754

lemma sg8635 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [5,5,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg931 sg1327

lemma sg8636 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [5,5,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg932 sg1327

lemma sg8637 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [5,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg923 sg1330

lemma sg8638 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [6,6,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg939 sg1327

lemma sg8639 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [7,7,6,1] := by
  exact rowSquare_join (by decide) sg13 sg4619

lemma sg8640 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [8,6,6,1] := by
  exact rowSquare_join (by decide) sg39 sg3764

lemma sg8641 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [8,7,5,1] := by
  exact rowSquare_join (by decide) sg39 sg3765

lemma sg8642 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [8,7,6] := by
  exact rowSquare_join (by decide) sg40 sg3764

lemma sg8643 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [8,8,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg4616

lemma sg8644 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [8,8,2,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg4617

lemma sg8645 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [8,8,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg4620

lemma sg8646 : RowSquare [6,5,2,1,1,1,1,1,1,1,1] [8,8,3,1,1] := by
  exact rowSquare_join (by decide) sg14 sg4618

lemma sg8647 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg534 sg1754

lemma sg8648 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg7232

lemma sg8649 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg535 sg1754

lemma sg8650 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg1327

lemma sg8651 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg536 sg1754

lemma sg8652 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg1754

lemma sg8653 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg7233

lemma sg8654 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg7234

lemma sg8655 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg534 sg1757

lemma sg8656 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg534 sg1758

lemma sg8657 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg541 sg1754

lemma sg8658 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg535 sg1755

lemma sg8659 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg838 sg1329

lemma sg8660 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg542 sg1754

lemma sg8661 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1261

lemma sg8662 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg838 sg1330

lemma sg8663 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg1755

lemma sg8664 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg838 sg1331

lemma sg8665 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg838 sg1332

lemma sg8666 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg543 sg1754

lemma sg8667 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg847 sg1327

lemma sg8668 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1262

lemma sg8669 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg536 sg1756

lemma sg8670 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1263

lemma sg8671 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg1756

lemma sg8672 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg1757

lemma sg8673 : RowSquare [6,5,2,2,1,1,1,1,1,1] [5,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg848 sg1327

lemma sg8674 : RowSquare [6,5,2,2,1,1,1,1,1,1] [5,5,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg544 sg1754

lemma sg8675 : RowSquare [6,5,2,2,1,1,1,1,1,1] [5,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg541 sg1755

lemma sg8676 : RowSquare [6,5,2,2,1,1,1,1,1,1] [5,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1264

lemma sg8677 : RowSquare [6,5,2,2,1,1,1,1,1,1] [5,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1265

lemma sg8678 : RowSquare [6,5,2,2,1,1,1,1,1,1] [6,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1266

lemma sg8679 : RowSquare [6,5,2,2,1,1,1,1,1,1] [7,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg545 sg1754

lemma sg8680 : RowSquare [6,5,2,2,1,1,1,1,1,1] [7,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg546 sg1754

lemma sg8681 : RowSquare [6,5,2,2,1,1,1,1,1,1] [7,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg547 sg1754

lemma sg8682 : RowSquare [6,5,2,2,2,2,1,1] [4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg5672

lemma sg8683 : RowSquare [6,5,2,2,2,2,1,1] [4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg5673

lemma sg8684 : RowSquare [6,5,2,2,2,2,1,1] [4,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg5675

lemma sg8685 : RowSquare [6,5,2,2,2,2,1,1] [4,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg5676

lemma sg8686 : RowSquare [6,5,2,2,2,2,1,1] [4,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg5677

lemma sg8687 : RowSquare [6,5,2,2,2,2,1,1] [4,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5 sg5678

lemma sg8688 : RowSquare [6,5,2,2,2,2,1,1] [4,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg5679

lemma sg8689 : RowSquare [6,5,2,2,2,2,1,1] [4,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg4 sg5695

lemma sg8690 : RowSquare [6,5,2,2,2,2,1,1] [4,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg4 sg5696

lemma sg8691 : RowSquare [6,5,2,2,2,2,1,1] [5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg5673

lemma sg8692 : RowSquare [6,5,2,2,2,2,1,1] [5,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg5675

lemma sg8693 : RowSquare [6,5,2,2,2,2,1,1] [5,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg5676

lemma sg8694 : RowSquare [6,5,2,2,2,2,1,1] [5,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg5677

lemma sg8695 : RowSquare [6,5,2,2,2,2,1,1] [5,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6 sg5678

lemma sg8696 : RowSquare [6,5,2,2,2,2,1,1] [5,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6 sg5679

lemma sg8697 : RowSquare [6,5,2,2,2,2,1,1] [5,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg5681

lemma sg8698 : RowSquare [6,5,2,2,2,2,1,1] [5,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg5682

lemma sg8699 : RowSquare [6,5,2,2,2,2,1,1] [5,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg5683

lemma sg8700 : RowSquare [6,5,2,2,2,2,1,1] [5,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg5684

lemma sg8701 : RowSquare [6,5,2,2,2,2,1,1] [5,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5699

lemma sg8702 : RowSquare [6,5,2,2,2,2,1,1] [5,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg5 sg5696

lemma sg8703 : RowSquare [6,5,2,2,2,2,1,1] [6,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg5681

lemma sg8704 : RowSquare [6,5,2,2,2,2,1,1] [6,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg5682

lemma sg8705 : RowSquare [6,5,2,2,2,2,1,1] [6,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg5683

lemma sg8706 : RowSquare [6,5,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6 sg5684

lemma sg8707 : RowSquare [6,6,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg889 sg1338

lemma sg8708 : RowSquare [6,6,1,1,1,1,1,1,1,1,1] [5,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg892 sg1338

lemma sg8709 : RowSquare [6,6,1,1,1,1,1,1,1,1,1] [6,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg905 sg1327

lemma sg8710 : RowSquare [6,6,1,1,1,1,1,1,1,1,1] [6,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg906 sg1327

lemma sg8711 : RowSquare [6,6,1,1,1,1,1,1,1,1,1] [6,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg900 sg1328

lemma sg8712 : RowSquare [6,6,1,1,1,1,1,1,1,1,1] [6,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg907 sg1327

lemma sg8713 : RowSquare [6,6,1,1,1,1,1,1,1,1,1] [6,5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg908 sg1327

lemma sg8714 : RowSquare [6,6,1,1,1,1,1,1,1,1,1] [6,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg902 sg1328

lemma sg8715 : RowSquare [6,6,1,1,1,1,1,1,1,1,1] [6,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg903 sg1328

lemma sg8716 : RowSquare [6,6,1,1,1,1,1,1,1,1,1] [6,5,5,5] := by
  exact rowSquare_join (by decide) sg13 sg4652

lemma sg8717 : RowSquare [6,6,1,1,1,1,1,1,1,1,1] [6,6,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg909 sg1327

lemma sg8718 : RowSquare [6,6,1,1,1,1,1,1,1,1,1] [6,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg889 sg1348

lemma sg8719 : RowSquare [6,6,1,1,1,1,1,1,1,1,1] [7,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg904 sg1332

lemma sg8720 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg807 sg1327

lemma sg8721 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg808 sg1327

lemma sg8722 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg809 sg1327

lemma sg8723 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg517 sg1754

lemma sg8724 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg810 sg1327

lemma sg8725 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6288

lemma sg8726 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg518 sg1754

lemma sg8727 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg811 sg1327

lemma sg8728 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg889 sg1257

lemma sg8729 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg519 sg1754

lemma sg8730 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg812 sg1327

lemma sg8731 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg890 sg1257

lemma sg8732 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg520 sg1754

lemma sg8733 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg813 sg1327

lemma sg8734 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg891 sg1257

lemma sg8735 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg892 sg1257

lemma sg8736 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg814 sg1327

lemma sg8737 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,4,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg815 sg1327

lemma sg8738 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg807 sg1329

lemma sg8739 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg816 sg1327

lemma sg8740 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg808 sg1329

lemma sg8741 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg809 sg1329

lemma sg8742 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,4,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg817 sg1327

lemma sg8743 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg807 sg1330

lemma sg8744 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg808 sg1330

lemma sg8745 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg809 sg1330

lemma sg8746 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg4673

lemma sg8747 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg808 sg1332

lemma sg8748 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg809 sg1332

lemma sg8749 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg521 sg1754

lemma sg8750 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg818 sg1327

lemma sg8751 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6289

lemma sg8752 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3 sg5525

lemma sg8753 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg819 sg1327

lemma sg8754 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6291

lemma sg8755 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg523 sg1754

lemma sg8756 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg820 sg1327

lemma sg8757 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg889 sg1260

lemma sg8758 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg821 sg1327

lemma sg8759 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg817 sg1328

lemma sg8760 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg4675

lemma sg8761 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg13 sg4677

lemma sg8762 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg892 sg1260

lemma sg8763 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,5,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg822 sg1327

lemma sg8764 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg814 sg1329

lemma sg8765 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg816 sg1329

lemma sg8766 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg814 sg1332

lemma sg8767 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,5,4,4,3] := by
  exact rowSquare_join (by decide) sg13 sg4679

lemma sg8768 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,5,5,3,3] := by
  exact rowSquare_join (by decide) sg892 sg1262

lemma sg8769 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg4682

lemma sg8770 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,5,5,5,1] := by
  exact rowSquare_join (by decide) sg13 sg4684

lemma sg8771 : RowSquare [6,6,2,1,1,1,1,1,1,1] [6,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg526 sg1754

lemma sg8772 : RowSquare [6,6,2,1,1,1,1,1,1,1] [6,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg824 sg1327

lemma sg8773 : RowSquare [6,6,2,1,1,1,1,1,1,1] [6,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg821 sg1328

lemma sg8774 : RowSquare [6,6,2,1,1,1,1,1,1,1] [6,5,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg530 sg1754

lemma sg8775 : RowSquare [6,6,2,1,1,1,1,1,1,1] [6,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg4691

lemma sg8776 : RowSquare [6,6,2,1,1,1,1,1,1,1] [6,5,5,5] := by
  exact rowSquare_join (by decide) sg26 sg3875

lemma sg8777 : RowSquare [6,6,2,1,1,1,1,1,1,1] [6,6,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg825 sg1327

lemma sg8778 : RowSquare [6,6,2,1,1,1,1,1,1,1] [6,6,3,3,3] := by
  exact rowSquare_join (by decide) sg14 sg4679

lemma sg8779 : RowSquare [6,6,2,1,1,1,1,1,1,1] [7,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg4694

lemma sg8781 : RowSquare [6,6,3,2,2,2] [2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg787 sg1180

lemma sg8782 : RowSquare [6,6,3,2,2,2] [3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg781 sg1180

lemma sg8783 : RowSquare [6,6,3,2,2,2] [4,4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg770 sg1180

lemma sg8784 : RowSquare [7,5,1,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg316 sg2251

lemma sg8785 : RowSquare [7,5,1,1,1,1,1,1,1,1,1] [4,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg317 sg2251

lemma sg8786 : RowSquare [7,5,1,1,1,1,1,1,1,1,1] [4,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg318 sg2251

lemma sg8787 : RowSquare [7,5,1,1,1,1,1,1,1,1,1] [4,4,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg319 sg2251

lemma sg8788 : RowSquare [7,5,1,1,1,1,1,1,1,1,1] [4,4,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg320 sg2251

lemma sg8789 : RowSquare [7,5,1,1,1,1,1,1,1,1,1] [5,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg322 sg2251

lemma sg8790 : RowSquare [7,5,1,1,1,1,1,1,1,1,1] [5,5,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg324 sg2251

lemma sg8791 : RowSquare [7,5,2,1,1,1,1,1,1,1] [3,3,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg270 sg2251

lemma sg8792 : RowSquare [7,5,2,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg586 sg1663

lemma sg8793 : RowSquare [7,5,2,1,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg271 sg2251

lemma sg8794 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg132 sg2702

lemma sg8795 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg272 sg2251

lemma sg8796 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6349

lemma sg8797 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6350

lemma sg8798 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg6288

lemma sg8799 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg133 sg2702

lemma sg8800 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg273 sg2251

lemma sg8801 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg7780

lemma sg8802 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg7781

lemma sg8803 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg7782

lemma sg8804 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg586 sg1664

lemma sg8805 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg134 sg2702

lemma sg8806 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg274 sg2251

lemma sg8807 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg7783

lemma sg8808 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg7784

lemma sg8809 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5414

lemma sg8810 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg5415

lemma sg8811 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg7786

lemma sg8812 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg7787

lemma sg8813 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg7788

lemma sg8814 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg7789

lemma sg8815 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,4,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg275 sg2251

lemma sg8816 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,4,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg276 sg2251

lemma sg8817 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,4,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg270 sg2253

lemma sg8818 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5416

lemma sg8819 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg271 sg2253

lemma sg8820 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5418

lemma sg8821 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5419

lemma sg8822 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg5420

lemma sg8823 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5421

lemma sg8824 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5422

lemma sg8825 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5423

lemma sg8826 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg4724

lemma sg8827 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg135 sg2702

lemma sg8828 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6351

lemma sg8829 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg6289

lemma sg8830 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg6290

lemma sg8831 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg136 sg2702

lemma sg8832 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6352

lemma sg8833 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg279 sg2251

lemma sg8834 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg4725

lemma sg8835 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg6292

lemma sg8836 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,4,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg137 sg2702

lemma sg8837 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,4,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg280 sg2251

lemma sg8838 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg7793

lemma sg8839 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg4726

lemma sg8840 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5427

lemma sg8841 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg0 sg7796

lemma sg8842 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,5,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg281 sg2251

lemma sg8843 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,5,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg275 sg2253

lemma sg8844 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg4741

lemma sg8845 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,5,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg276 sg2253

lemma sg8846 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg4727

lemma sg8847 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5428

lemma sg8848 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg5430

lemma sg8849 : RowSquare [7,5,2,1,1,1,1,1,1,1] [6,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg138 sg2702

lemma sg8850 : RowSquare [7,5,2,1,1,1,1,1,1,1] [6,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg282 sg2251

lemma sg8851 : RowSquare [7,5,2,1,1,1,1,1,1,1] [6,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6353

lemma sg8852 : RowSquare [7,5,2,1,1,1,1,1,1,1] [6,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg139 sg2702

lemma sg8853 : RowSquare [7,5,2,1,1,1,1,1,1,1] [6,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg283 sg2251

lemma sg8854 : RowSquare [7,5,2,1,1,1,1,1,1,1] [6,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6354

lemma sg8855 : RowSquare [7,5,2,1,1,1,1,1,1,1] [6,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6355

lemma sg8856 : RowSquare [7,5,2,1,1,1,1,1,1,1] [6,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg284 sg2251

lemma sg8857 : RowSquare [7,5,2,1,1,1,1,1,1,1] [6,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6356

lemma sg8858 : RowSquare [7,5,2,1,1,1,1,1,1,1] [6,5,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg7798

lemma sg8859 : RowSquare [7,5,2,1,1,1,1,1,1,1] [6,6,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg281 sg2253

lemma sg8860 : RowSquare [7,6,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg5525

lemma sg8861 : RowSquare [7,6,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg5525

lemma sg8862 : RowSquare [7,6,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg5526

lemma sg8863 : RowSquare [7,6,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg4740

lemma sg8864 : RowSquare [7,6,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5527

lemma sg8865 : RowSquare [7,6,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg4741

lemma sg8866 : RowSquare [7,6,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg4742

lemma sg8867 : RowSquare [7,6,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5528

lemma sg8868 : RowSquare [7,6,1,1,1,1,1,1,1,1] [4,4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg4743

lemma sg8869 : RowSquare [7,6,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg4744

lemma sg8870 : RowSquare [7,6,1,1,1,1,1,1,1,1] [4,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg4745

lemma sg8871 : RowSquare [7,6,1,1,1,1,1,1,1,1] [5,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg260 sg2251

lemma sg8872 : RowSquare [7,6,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6391

lemma sg8873 : RowSquare [7,6,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6 sg5525

lemma sg8874 : RowSquare [7,6,1,1,1,1,1,1,1,1] [5,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg261 sg2251

lemma sg8875 : RowSquare [7,6,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6393

lemma sg8876 : RowSquare [7,6,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg5526

lemma sg8877 : RowSquare [7,6,1,1,1,1,1,1,1,1] [5,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg262 sg2251

lemma sg8878 : RowSquare [7,6,1,1,1,1,1,1,1,1] [5,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6395

lemma sg8879 : RowSquare [7,6,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5530

lemma sg8880 : RowSquare [7,6,1,1,1,1,1,1,1,1] [5,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6397

lemma sg8881 : RowSquare [7,6,1,1,1,1,1,1,1,1] [5,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6398

lemma sg8882 : RowSquare [7,6,1,1,1,1,1,1,1,1] [5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg0 sg7807

lemma sg8883 : RowSquare [7,6,1,1,1,1,1,1,1,1] [5,5,4,4,3] := by
  exact rowSquare_join (by decide) sg13 sg4751

lemma sg8884 : RowSquare [7,6,1,1,1,1,1,1,1,1] [5,5,5,3,3] := by
  exact rowSquare_join (by decide) sg4 sg5550

lemma sg8885 : RowSquare [7,6,1,1,1,1,1,1,1,1] [5,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg4752

lemma sg8886 : RowSquare [7,6,1,1,1,1,1,1,1,1] [5,5,5,5,1] := by
  exact rowSquare_join (by decide) sg13 sg4753

lemma sg8887 : RowSquare [7,6,1,1,1,1,1,1,1,1] [6,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg263 sg2251

lemma sg8888 : RowSquare [7,6,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6399

lemma sg8889 : RowSquare [7,6,1,1,1,1,1,1,1,1] [6,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg4754

lemma sg8890 : RowSquare [8,3,2,2,2,2,2] [6,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg165 sg2550

lemma sg8891 : RowSquare [8,4,3,2,1,1,1,1] [2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1056 sg1129

lemma sg8892 : RowSquare [8,4,3,2,1,1,1,1] [2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1056 sg1128

lemma sg8893 : RowSquare [9,3,2,2,2,2,1] [4,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg3209

lemma sg8894 : RowSquare [9,3,2,2,2,2,1] [5,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg74 sg3213

lemma sg8895 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,4] := by
  exact rowSquare_join (by decide) sg1105 sg1980

lemma sg8896 : RowSquare [4,3,2,2,2,2,1,1,1,1,1,1,1] [5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1416 sg1538

lemma sg8897 : RowSquare [4,3,2,2,2,2,1,1,1,1,1,1,1] [5,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1416 sg1539

lemma sg8898 : RowSquare [4,3,2,2,2,2,1,1,1,1,1,1,1] [5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg1032 sg1926

lemma sg8899 : RowSquare [4,3,2,2,2,2,1,1,1,1,1,1,1] [5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg1033 sg1926

lemma sg8900 : RowSquare [4,3,2,2,2,2,1,1,1,1,1,1,1] [6,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1417 sg1541

lemma sg8901 : RowSquare [4,3,2,2,2,2,1,1,1,1,1,1,1] [6,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1460 sg1518

lemma sg8902 : RowSquare [4,3,2,2,2,2,1,1,1,1,1,1,1] [6,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1417 sg1542

lemma sg8903 : RowSquare [4,3,2,2,2,2,1,1,1,1,1,1,1] [6,6,5,5] := by
  exact rowSquare_join (by decide) sg1072 sg1908

lemma sg8904 : RowSquare [4,3,2,2,2,2,1,1,1,1,1,1,1] [6,6,6,4] := by
  exact rowSquare_join (by decide) sg1539 sg1426

lemma sg8905 : RowSquare [4,3,2,2,2,2,1,1,1,1,1,1,1] [7,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1524 sg1460

lemma sg8906 : RowSquare [4,3,2,2,2,2,1,1,1,1,1,1,1] [7,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1417 sg1547

lemma sg8907 : RowSquare [4,3,2,2,2,2,1,1,1,1,1,1,1] [8,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1289 sg1570

lemma sg8908 : RowSquare [4,3,2,2,2,2,1,1,1,1,1,1,1] [8,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1289 sg1572

lemma sg8909 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1,1,1,1] [8,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1517 sg1552

lemma sg8910 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1,1,1,1] [8,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1552 sg1518

lemma sg8911 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1,1,1,1] [9,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1524 sg1552

lemma sg8912 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1416 sg1517

lemma sg8913 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [5,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1417 sg1517

lemma sg8914 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1417 sg1518

lemma sg8915 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1416 sg1520

lemma sg8916 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1032 sg1903

lemma sg8917 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1417 sg1520

lemma sg8918 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [5,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1031 sg1904

lemma sg8919 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1032 sg1905

lemma sg8920 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1033 sg1905

lemma sg8921 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg1032 sg1908

lemma sg8922 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg1033 sg1908

lemma sg8923 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1416 sg1524

lemma sg8924 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [6,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1524 sg1417

lemma sg8925 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1034 sg1903

lemma sg8926 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [6,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1416 sg1525

lemma sg8927 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [6,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1417 sg1525

lemma sg8928 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [6,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1517 sg1419

lemma sg8929 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [6,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1418 sg1520

lemma sg8930 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [6,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1517 sg1422

lemma sg8931 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [6,6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1520 sg1422

lemma sg8932 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [6,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1032 sg1913

lemma sg8933 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [6,6,5,5] := by
  exact rowSquare_join (by decide) sg1040 sg1908

lemma sg8934 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [7,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1418 sg1524

lemma sg8935 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [7,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1416 sg1530

lemma sg8936 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [7,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1417 sg1530

lemma sg8937 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [7,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1418 sg1525

end UniversalTensorSquare
end
end

end OAI
