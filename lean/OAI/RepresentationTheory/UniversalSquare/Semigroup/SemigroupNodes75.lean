import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes51
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes21
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes24
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes44
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes39
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes41

namespace OAI

/-! Semigroup Nodes 75. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg30540 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10486

lemma sg30541 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6954 sg11475

lemma sg30542 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9315

lemma sg30543 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9355

lemma sg30544 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9971

lemma sg30545 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8345 sg10725

lemma sg30546 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9971

lemma sg30547 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9315

lemma sg30548 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9946

lemma sg30549 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9946

lemma sg30550 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8347 sg10713

lemma sg30551 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9622

lemma sg30552 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10382

lemma sg30553 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9316

lemma sg30554 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9947

lemma sg30555 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9947

lemma sg30556 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10382

lemma sg30557 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9939

lemma sg30558 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9623

lemma sg30559 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9621

lemma sg30560 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9357

lemma sg30561 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9940

lemma sg30562 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9624

lemma sg30563 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8808 sg9279

lemma sg30564 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,6,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5577 sg12626

lemma sg30565 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,6,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6001 sg11832

lemma sg30566 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,6,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10380

lemma sg30567 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,6,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9355

lemma sg30568 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,6,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9972

lemma sg30569 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,6,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8345 sg10726

lemma sg30570 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,6,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9972

lemma sg30571 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,6,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10383

lemma sg30572 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,6,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9317

lemma sg30573 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,6,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9948

lemma sg30574 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,6,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9948

lemma sg30575 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,6,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10383

lemma sg30576 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,6,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9941

lemma sg30577 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,6,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9625

lemma sg30578 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,6,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9359

lemma sg30579 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,6,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9942

lemma sg30580 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,6,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9626

lemma sg30581 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,6,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9623

lemma sg30582 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,6,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9940

lemma sg30583 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,6,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9624

lemma sg30584 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,6,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9624

lemma sg30585 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,7,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6015 sg11829

lemma sg30586 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,7,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10384

lemma sg30587 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,7,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9318

lemma sg30588 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,7,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9949

lemma sg30589 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,7,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9949

lemma sg30590 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,7,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10384

lemma sg30591 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,7,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9292

lemma sg30592 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,7,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9292

lemma sg30593 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,7,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9292

lemma sg30594 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,7,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9625

lemma sg30595 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,7,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9942

lemma sg30596 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,7,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9626

lemma sg30597 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,7,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9626

lemma sg30598 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2205 sg15563

lemma sg30599 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2242 sg15529

lemma sg30600 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3167 sg14804

lemma sg30601 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3774 sg14541

lemma sg30602 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5277 sg12682

lemma sg30603 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5261 sg12691

lemma sg30604 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9283

lemma sg30605 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8877 sg9065

lemma sg30606 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8666 sg9795

lemma sg30607 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3168 sg14804

lemma sg30608 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3775 sg14541

lemma sg30609 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5268 sg12689

lemma sg30610 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6600 sg11540

lemma sg30611 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9284

lemma sg30612 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8806 sg9283

lemma sg30613 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8666 sg9796

lemma sg30614 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8742 sg9546

lemma sg30615 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5850 sg11839

lemma sg30616 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6601 sg11540

lemma sg30617 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9319

lemma sg30618 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9360

lemma sg30619 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8807 sg9283

lemma sg30620 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8878 sg9065

lemma sg30621 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9286

lemma sg30622 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9319

lemma sg30623 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9943

lemma sg30624 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10158

lemma sg30625 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8565 sg10116

lemma sg30626 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9319

lemma sg30627 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9319

lemma sg30628 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9319

lemma sg30629 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8773 sg9458

lemma sg30630 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3776 sg14541

lemma sg30631 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,4,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5851 sg11839

lemma sg30632 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,4,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6602 sg11540

lemma sg30633 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9287

lemma sg30634 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9360

lemma sg30635 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9283

lemma sg30636 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8880 sg9065

lemma sg30637 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,4,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6603 sg11540

lemma sg30638 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,4,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9320

lemma sg30639 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,4,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9361

lemma sg30640 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9973

lemma sg30641 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10159

lemma sg30642 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9973

lemma sg30643 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9320

lemma sg30644 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9320

lemma sg30645 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9320

lemma sg30646 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9320

lemma sg30647 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9627

lemma sg30648 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,4,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9321

lemma sg30649 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,4,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9321

lemma sg30650 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9321

lemma sg30651 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9321

lemma sg30652 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9321

lemma sg30653 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9945

lemma sg30654 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9628

lemma sg30655 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8808 sg9286

lemma sg30656 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,5,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5852 sg11839

lemma sg30657 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,5,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6604 sg11540

lemma sg30658 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,5,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9290

lemma sg30659 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,5,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9361

lemma sg30660 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9974

lemma sg30661 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,5,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10160

lemma sg30662 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9974

lemma sg30663 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,5,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9322

lemma sg30664 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,5,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9322

lemma sg30665 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,5,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9322

lemma sg30666 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,5,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9322

lemma sg30667 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9322

lemma sg30668 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9946

lemma sg30669 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,5,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9629

lemma sg30670 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,5,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9362

lemma sg30671 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,5,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9947

lemma sg30672 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,5,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9630

lemma sg30673 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,5,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9628

lemma sg30674 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8807 sg9289

lemma sg30675 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,5,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8808 sg9289

lemma sg30676 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,6,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6605 sg11540

lemma sg30677 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,6,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9323

lemma sg30678 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,6,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9323

lemma sg30679 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,6,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9323

lemma sg30680 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,6,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9323

lemma sg30681 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,6,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9323

lemma sg30682 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,6,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9363

lemma sg30683 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,6,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9948

lemma sg30684 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,6,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9631

lemma sg30685 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,6,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9629

lemma sg30686 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,6,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9947

lemma sg30687 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,6,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9630

lemma sg30688 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,6,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9630

lemma sg30689 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,7,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10384

lemma sg30690 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,7,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9364

lemma sg30691 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,7,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9949

lemma sg30692 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,7,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9632

lemma sg30693 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,7,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9948

lemma sg30694 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,7,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9631

lemma sg30695 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,7,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9631

lemma sg30696 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,8,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9364

lemma sg30697 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,8,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9949

lemma sg30698 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,8,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9632

lemma sg30699 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,8,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9632

lemma sg30700 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1317 sg20975

lemma sg30701 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1719 sg18255

lemma sg30702 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg963 sg21132

lemma sg30703 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1814 sg17137

lemma sg30704 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg342 sg21311

lemma sg30705 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2667 sg15033

lemma sg30706 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg342 sg21312

lemma sg30707 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,2,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg342 sg21313

lemma sg30708 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg342 sg21314

lemma sg30709 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg342 sg21315

lemma sg30710 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1318 sg20975

lemma sg30711 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1720 sg18255

lemma sg30712 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1827 sg17122

lemma sg30713 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2194 sg15571

lemma sg30714 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2230 sg15536

lemma sg30715 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2676 sg15022

lemma sg30716 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2667 sg15034

lemma sg30717 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg575 sg21224

lemma sg30718 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg575 sg21225

lemma sg30719 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg575 sg21226

lemma sg30720 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1721 sg18255

lemma sg30721 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1463 sg20942

lemma sg30722 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1816 sg17137

lemma sg30723 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2223 sg15549

lemma sg30724 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2668 sg15033

lemma sg30725 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg868 sg21155

lemma sg30726 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3513 sg14694

lemma sg30727 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg868 sg21156

lemma sg30728 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg868 sg21157

lemma sg30729 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg868 sg21158

lemma sg30730 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1836 sg17110

lemma sg30731 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1854 sg16205

lemma sg30732 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2237 sg15532

lemma sg30733 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1814 sg17138

lemma sg30734 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5536 sg12632

lemma sg30735 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1288 sg21034

lemma sg30736 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10385

lemma sg30737 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8366 sg10682

lemma sg30738 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3870 sg14520

lemma sg30739 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2237 sg15533

lemma sg30740 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6943 sg11476

lemma sg30741 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5592 sg12611

lemma sg30742 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8836 sg9198

lemma sg30743 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8542 sg10132

lemma sg30744 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8726 sg9580

lemma sg30745 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5834 sg11840

lemma sg30746 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6571 sg11542

lemma sg30747 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10487

lemma sg30748 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8842 sg9180

lemma sg30749 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8649 sg9950

lemma sg30750 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8572 sg10105

lemma sg30751 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8842 sg9181

lemma sg30752 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9975

lemma sg30753 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8650 sg9950

lemma sg30754 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10820

lemma sg30755 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10487

lemma sg30756 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8648 sg9975

lemma sg30757 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1319 sg20975

lemma sg30758 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1722 sg18255

lemma sg30759 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1828 sg17122

lemma sg30760 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2195 sg15571

lemma sg30761 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2224 sg15549

lemma sg30762 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2677 sg15022

lemma sg30763 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg850 sg21178

lemma sg30764 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3514 sg14691

lemma sg30765 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg869 sg21156

lemma sg30766 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg869 sg21157

lemma sg30767 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg869 sg21158

lemma sg30768 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1829 sg17122

lemma sg30769 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2196 sg15571

lemma sg30770 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2225 sg15549

lemma sg30771 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2670 sg15033

lemma sg30772 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2867 sg14863

lemma sg30773 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5539 sg12632

lemma sg30774 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3514 sg14692

lemma sg30775 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10385

lemma sg30776 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8369 sg10682

lemma sg30777 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2226 sg15549

lemma sg30778 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3871 sg14520

lemma sg30779 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2237 sg15535

lemma sg30780 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6944 sg11476

lemma sg30781 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5536 sg12633

lemma sg30782 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10386

lemma sg30783 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8438 sg10308

lemma sg30784 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8729 sg9580

lemma sg30785 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2669 sg15034

lemma sg30786 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6945 sg11476

lemma sg30787 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6572 sg11542

lemma sg30788 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10403

lemma sg30789 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8837 sg9198

lemma sg30790 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8651 sg9950

lemma sg30791 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6573 sg11542

lemma sg30792 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10488

lemma sg30793 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10403

lemma sg30794 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9951

lemma sg30795 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8720 sg9633

lemma sg30796 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8842 sg9184

lemma sg30797 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10821

lemma sg30798 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10488

lemma sg30799 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10403

lemma sg30800 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9976

lemma sg30801 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1819 sg17137

lemma sg30802 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2227 sg15549

lemma sg30803 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3872 sg14520

lemma sg30804 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2873 sg14856

lemma sg30805 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6946 sg11476

lemma sg30806 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5593 sg12611

lemma sg30807 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8799 sg9293

lemma sg30808 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8547 sg10132

lemma sg30809 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8732 sg9580

lemma sg30810 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3164 sg14805

lemma sg30811 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3770 sg14542

lemma sg30812 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5543 sg12632

lemma sg30813 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5963 sg11838

lemma sg30814 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10387

lemma sg30815 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9293

lemma sg30816 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8652 sg9950

lemma sg30817 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6947 sg11476

lemma sg30818 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6574 sg11542

lemma sg30819 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8799 sg9295

lemma sg30820 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8815 sg9262

lemma sg30821 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9293

lemma sg30822 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8721 sg9633

lemma sg30823 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10489

lemma sg30824 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8815 sg9263

lemma sg30825 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10822

lemma sg30826 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10489

lemma sg30827 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9977

lemma sg30828 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10161

lemma sg30829 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9977

lemma sg30830 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8423 sg10387

lemma sg30831 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3778 sg14539

lemma sg30832 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6948 sg11476

lemma sg30833 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6575 sg11542

lemma sg30834 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10388

lemma sg30835 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9294

lemma sg30836 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8657 sg9812

lemma sg30837 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8722 sg9633

lemma sg30838 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6016 sg11827

lemma sg30839 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10490

lemma sg30840 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9295

lemma sg30841 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10823

lemma sg30842 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10490

lemma sg30843 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10404

lemma sg30844 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9978

lemma sg30845 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10404

lemma sg30846 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9978

lemma sg30847 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9953

lemma sg30848 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10388

lemma sg30849 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8610 sg10079

lemma sg30850 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8372 sg10682

lemma sg30851 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9979

lemma sg30852 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10162

lemma sg30853 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9979

lemma sg30854 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9954

lemma sg30855 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9954

lemma sg30856 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10389

lemma sg30857 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,4,4,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9296

lemma sg30858 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1723 sg18255

lemma sg30859 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1830 sg17122

lemma sg30860 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2197 sg15571

lemma sg30861 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2234 sg15536

lemma sg30862 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2678 sg15022

lemma sg30863 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2868 sg14863

lemma sg30864 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5562 sg12630

lemma sg30865 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3514 sg14693

lemma sg30866 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8443 sg10308

lemma sg30867 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8383 sg10641

lemma sg30868 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2198 sg15571

lemma sg30869 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2235 sg15536

lemma sg30870 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3890 sg14510

lemma sg30871 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2869 sg14863

lemma sg30872 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6994 sg11469

lemma sg30873 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5539 sg12633

lemma sg30874 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10386

lemma sg30875 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8444 sg10308

lemma sg30876 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8660 sg9810

lemma sg30877 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3873 sg14520

lemma sg30878 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3770 sg14543

lemma sg30879 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6949 sg11476

lemma sg30880 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6576 sg11542

lemma sg30881 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10390

lemma sg30882 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9365

lemma sg30883 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8729 sg9581

lemma sg30884 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6995 sg11469

lemma sg30885 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6577 sg11542

lemma sg30886 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10405

lemma sg30887 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8816 sg9262

lemma sg30888 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9951

lemma sg30889 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8730 sg9581

lemma sg30890 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10491

lemma sg30891 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10405

lemma sg30892 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10824

lemma sg30893 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10491

lemma sg30894 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9980

lemma sg30895 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10405

lemma sg30896 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9980

lemma sg30897 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8423 sg10390

lemma sg30898 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2236 sg15536

lemma sg30899 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3874 sg14520

lemma sg30900 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3771 sg14542

lemma sg30901 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6950 sg11476

lemma sg30902 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6578 sg11542

lemma sg30903 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10387

lemma sg30904 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9365

lemma sg30905 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8732 sg9581

lemma sg30906 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3772 sg14542

lemma sg30907 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6951 sg11476

lemma sg30908 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6579 sg11542

lemma sg30909 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10391

lemma sg30910 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9366

lemma sg30911 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9951

lemma sg30912 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8733 sg9581

lemma sg30913 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6580 sg11542

lemma sg30914 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10492

lemma sg30915 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8806 sg9295

lemma sg30916 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10825

lemma sg30917 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10492

lemma sg30918 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10406

lemma sg30919 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9981

lemma sg30920 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10406

lemma sg30921 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9981

lemma sg30922 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9956

lemma sg30923 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10391

lemma sg30924 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6952 sg11476

lemma sg30925 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6581 sg11542

lemma sg30926 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10493

lemma sg30927 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9367

lemma sg30928 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10826

lemma sg30929 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10493

lemma sg30930 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10407

lemma sg30931 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10407

lemma sg30932 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9982

lemma sg30933 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10407

lemma sg30934 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9982

lemma sg30935 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9957

lemma sg30936 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9957

lemma sg30937 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10392

lemma sg30938 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8376 sg10682

lemma sg30939 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9958

end UniversalTensorSquare
end
end

end OAI
