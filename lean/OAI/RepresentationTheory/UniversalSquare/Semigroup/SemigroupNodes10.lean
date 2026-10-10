import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes8

namespace OAI

/-! Semigroup Nodes 10. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4516 : RowSquare [10,1,1,1,1,1,1] [8,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg1751

lemma sg4517 : RowSquare [10,2,1,1,1,1] [5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg45 sg1331

lemma sg4518 : RowSquare [10,2,1,1,1,1] [5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg1331

lemma sg4519 : RowSquare [10,2,2,1,1] [4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg87 sg1001

lemma sg4520 : RowSquare [10,2,2,1,1] [4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg999

lemma sg4521 : RowSquare [10,2,2,2] [4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg371 sg371

lemma sg4522 : RowSquare [10,2,2,2] [4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg371 sg372

lemma sg4523 : RowSquare [10,2,2,2] [4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg371 sg373

lemma sg4524 : RowSquare [10,2,2,2] [4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg372 sg372

lemma sg4525 : RowSquare [10,2,2,2] [4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg372 sg373

lemma sg4526 : RowSquare [10,2,2,2] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg373 sg373

lemma sg4527 : RowSquare [10,2,2,2] [5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg371 sg377

lemma sg4528 : RowSquare [10,2,2,2] [5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg378

lemma sg4529 : RowSquare [10,2,2,2] [5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg372 sg377

lemma sg4530 : RowSquare [10,2,2,2] [5,5,3,3] := by
  exact rowSquare_join (by decide) sg373 sg377

lemma sg4531 : RowSquare [10,2,2,2] [5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg372 sg378

lemma sg4532 : RowSquare [10,2,2,2] [5,5,4,2] := by
  exact rowSquare_join (by decide) sg373 sg378

lemma sg4533 : RowSquare [10,3,1,1,1] [4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg998

lemma sg4534 : RowSquare [10,3,1,1,1] [4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg999

lemma sg4535 : RowSquare [10,3,1,1,1] [4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg97 sg1001

lemma sg4536 : RowSquare [10,3,2,1] [4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg371 sg390

lemma sg4537 : RowSquare [10,3,2,1] [4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg88 sg1033

lemma sg4538 : RowSquare [10,3,2,1] [4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg89 sg1032

lemma sg4539 : RowSquare [10,3,2,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg390 sg373

lemma sg4540 : RowSquare [10,3,3] [5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg88 sg1063

lemma sg4541 : RowSquare [10,3,3] [5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg1063

lemma sg4542 : RowSquare [10,3,3] [5,5,3,3] := by
  exact rowSquare_join (by decide) sg88 sg1064

lemma sg4543 : RowSquare [10,4,2] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg390 sg390

lemma sg4544 : RowSquare [11,2,1,1,1] [6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg231 sg586

lemma sg4545 : RowSquare [11,2,1,1,1] [6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg232 sg586

lemma sg4546 : RowSquare [11,2,1,1,1] [6,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg104 sg998

lemma sg4547 : RowSquare [11,2,1,1,1] [6,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg104 sg1000

lemma sg4548 : RowSquare [11,2,1,1,1] [6,3,3,2,2] := by
  exact rowSquare_join (by decide) sg104 sg1001

lemma sg4549 : RowSquare [11,2,1,1,1] [6,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg105 sg998

lemma sg4550 : RowSquare [11,2,1,1,1] [6,4,2,2,2] := by
  exact rowSquare_join (by decide) sg105 sg1001

lemma sg4551 : RowSquare [11,2,1,1,1] [7,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg233 sg586

lemma sg4552 : RowSquare [11,2,1,1,1] [7,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg231 sg587

lemma sg4553 : RowSquare [11,2,1,1,1] [7,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg232 sg587

lemma sg4554 : RowSquare [3,3,2,1,1,1,1,1,1,1,1,1] [7,3,3,2,2] := by
  exact rowSquare_join (by decide) sg389 sg708

lemma sg4555 : RowSquare [3,3,2,1,1,1,1,1,1,1,1,1] [7,3,3,3,1] := by
  exact rowSquare_join (by decide) sg413 sg693

lemma sg4556 : RowSquare [3,3,2,1,1,1,1,1,1,1,1,1] [7,4,2,2,2] := by
  exact rowSquare_join (by decide) sg413 sg694

lemma sg4557 : RowSquare [3,3,2,1,1,1,1,1,1,1,1,1] [7,4,3,2,1] := by
  exact rowSquare_join (by decide) sg389 sg709

lemma sg4558 : RowSquare [3,3,2,1,1,1,1,1,1,1,1,1] [7,4,3,3] := by
  exact rowSquare_join (by decide) sg390 sg709

lemma sg4559 : RowSquare [3,3,2,2,1,1,1,1,1,1,1] [6,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg391 sg692

lemma sg4560 : RowSquare [3,3,2,2,1,1,1,1,1,1,1] [6,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg391 sg693

lemma sg4561 : RowSquare [3,3,2,2,1,1,1,1,1,1,1] [6,3,3,3,2] := by
  exact rowSquare_join (by decide) sg413 sg644

lemma sg4562 : RowSquare [3,3,2,2,1,1,1,1,1,1,1] [7,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg391 sg697

lemma sg4563 : RowSquare [3,3,2,2,1,1,1,1,1,1,1] [8,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg306 sg716

lemma sg4564 : RowSquare [3,3,2,2,1,1,1,1,1,1,1] [8,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg391 sg702

lemma sg4565 : RowSquare [3,3,2,2,1,1,1,1,1,1,1] [8,3,3,3] := by
  exact rowSquare_join (by decide) sg390 sg704

lemma sg4566 : RowSquare [3,3,2,2,2,2,2,1] [4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg306 sg656

lemma sg4567 : RowSquare [3,3,2,2,2,2,2,1] [4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg306 sg657

lemma sg4568 : RowSquare [3,3,2,2,2,2,2,1] [4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg306 sg658

lemma sg4569 : RowSquare [3,3,3,2,1,1,1,1,1,1] [4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg193 sg1061

lemma sg4570 : RowSquare [3,3,3,2,1,1,1,1,1,1] [4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg74 sg1533

lemma sg4571 : RowSquare [3,3,3,2,1,1,1,1,1,1] [4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg194 sg1061

lemma sg4572 : RowSquare [3,3,3,2,1,1,1,1,1,1] [4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg389 sg636

lemma sg4573 : RowSquare [3,3,3,2,1,1,1,1,1,1] [4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg390 sg636

lemma sg4574 : RowSquare [3,3,3,2,1,1,1,1,1,1] [4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg389 sg637

lemma sg4575 : RowSquare [3,3,3,2,1,1,1,1,1,1] [4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg390 sg637

lemma sg4576 : RowSquare [3,3,3,2,1,1,1,1,1,1] [5,4,4,4] := by
  exact rowSquare_join (by decide) sg390 sg638

lemma sg4577 : RowSquare [3,3,3,2,1,1,1,1,1,1] [5,5,4,3] := by
  exact rowSquare_join (by decide) sg390 sg640

lemma sg4578 : RowSquare [3,3,3,2,1,1,1,1,1,1] [7,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg348 sg703

lemma sg4579 : RowSquare [3,3,3,2,1,1,1,1,1,1] [7,7,1,1,1] := by
  exact rowSquare_join (by decide) sg396 sg639

lemma sg4580 : RowSquare [4,3,1,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg371 sg708

lemma sg4581 : RowSquare [4,3,1,1,1,1,1,1,1,1,1,1] [7,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg371 sg709

lemma sg4582 : RowSquare [4,3,1,1,1,1,1,1,1,1,1,1] [7,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg710

lemma sg4583 : RowSquare [4,3,1,1,1,1,1,1,1,1,1,1] [7,4,3,3] := by
  exact rowSquare_join (by decide) sg373 sg709

lemma sg4584 : RowSquare [4,3,1,1,1,1,1,1,1,1,1,1] [8,3,3,3] := by
  exact rowSquare_join (by decide) sg373 sg711

lemma sg4585 : RowSquare [4,3,1,1,1,1,1,1,1,1,1,1] [8,4,3,2] := by
  exact rowSquare_join (by decide) sg373 sg712

lemma sg4586 : RowSquare [4,3,1,1,1,1,1,1,1,1,1,1] [8,5,2,2] := by
  exact rowSquare_join (by decide) sg373 sg713

lemma sg4587 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg370 sg692

lemma sg4588 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg693

lemma sg4589 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg218 sg1032

lemma sg4590 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg218 sg1033

lemma sg4591 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg370 sg694

lemma sg4592 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg695

lemma sg4593 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg371 sg692

lemma sg4594 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg371 sg693

lemma sg4595 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg219 sg1033

lemma sg4596 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg696

lemma sg4597 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg220 sg1032

lemma sg4598 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg389 sg675

lemma sg4599 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg389 sg676

lemma sg4600 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [5,4,4,4] := by
  exact rowSquare_join (by decide) sg390 sg676

lemma sg4601 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg1109

lemma sg4602 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg371 sg694

lemma sg4603 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg1110

lemma sg4604 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg371 sg695

lemma sg4605 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg372 sg694

lemma sg4606 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg373 sg694

lemma sg4607 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg696

lemma sg4608 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg372 sg695

lemma sg4609 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [5,5,4,3] := by
  exact rowSquare_join (by decide) sg373 sg695

lemma sg4610 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg372 sg696

lemma sg4611 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [5,5,5,2] := by
  exact rowSquare_join (by decide) sg373 sg696

lemma sg4612 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg370 sg697

lemma sg4613 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [6,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg370 sg698

lemma sg4614 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [6,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg371 sg697

lemma sg4615 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [6,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg391 sg675

lemma sg4616 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg1112

lemma sg4617 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [6,6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg701

lemma sg4618 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [6,6,3,1,1] := by
  exact rowSquare_join (by decide) sg372 sg701

lemma sg4619 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [6,6,5] := by
  exact rowSquare_join (by decide) sg378 sg696

lemma sg4620 : RowSquare [4,3,2,1,1,1,1,1,1,1,1] [7,7,1,1,1] := by
  exact rowSquare_join (by decide) sg383 sg694

lemma sg4621 : RowSquare [4,3,2,2,1,1,1,1,1,1] [4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg693

lemma sg4622 : RowSquare [4,3,2,2,1,1,1,1,1,1] [4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg696

lemma sg4623 : RowSquare [4,3,2,2,1,1,1,1,1,1] [4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg390 sg616

lemma sg4624 : RowSquare [4,3,2,2,2,2,1,1] [3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg330 sg579

lemma sg4625 : RowSquare [4,3,2,2,2,2,1,1] [4,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg208 sg849

lemma sg4626 : RowSquare [4,3,2,2,2,2,1,1] [4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg330 sg581

lemma sg4627 : RowSquare [4,3,2,2,2,2,1,1] [4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg209 sg849

lemma sg4628 : RowSquare [4,3,2,2,2,2,1,1] [4,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg210 sg849

lemma sg4629 : RowSquare [4,3,2,2,2,2,1,1] [4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg583

lemma sg4630 : RowSquare [4,3,2,2,2,2,1,1] [4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg584

lemma sg4631 : RowSquare [4,3,2,2,2,2,1,1] [5,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg211 sg849

lemma sg4632 : RowSquare [4,3,2,2,2,2,1,1] [5,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg212 sg849

lemma sg4633 : RowSquare [4,3,2,2,2,2,1,1] [5,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg213 sg849

lemma sg4634 : RowSquare [4,3,2,2,2,2,1,1] [6,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg214 sg849

lemma sg4635 : RowSquare [4,3,2,2,2,2,1,1] [6,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg215 sg849

lemma sg4636 : RowSquare [4,3,2,2,2,2,1,1] [7,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg216 sg849

lemma sg4637 : RowSquare [4,3,3,2,1,1,1,1,1] [4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg641

lemma sg4638 : RowSquare [4,3,3,2,1,1,1,1,1] [4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg980

lemma sg4639 : RowSquare [4,3,3,2,1,1,1,1,1] [5,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg104 sg1232

lemma sg4640 : RowSquare [4,3,3,2,1,1,1,1,1] [5,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg105 sg1232

lemma sg4641 : RowSquare [4,3,3,2,1,1,1,1,1] [5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg220 sg850

lemma sg4642 : RowSquare [4,3,3,2,1,1,1,1,1] [6,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg106 sg1232

lemma sg4643 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg370 sg673

lemma sg4644 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg370 sg674

lemma sg4645 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg370 sg675

lemma sg4646 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg676

lemma sg4647 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg371 sg674

lemma sg4648 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg371 sg675

lemma sg4649 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg371 sg676

lemma sg4650 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg372 sg675

lemma sg4651 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg372 sg676

lemma sg4652 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [5,4,4,4] := by
  exact rowSquare_join (by decide) sg373 sg676

lemma sg4653 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg370 sg677

lemma sg4654 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg370 sg678

lemma sg4655 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg371 sg677

lemma sg4656 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg374 sg675

lemma sg4657 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [6,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg374 sg676

lemma sg4658 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [6,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg681

lemma sg4659 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [6,5,3,2,1] := by
  exact rowSquare_join (by decide) sg372 sg680

lemma sg4660 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [6,5,3,3] := by
  exact rowSquare_join (by decide) sg373 sg680

lemma sg4661 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [6,5,4,1,1] := by
  exact rowSquare_join (by decide) sg372 sg681

lemma sg4662 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [6,5,4,2] := by
  exact rowSquare_join (by decide) sg373 sg681

lemma sg4663 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg370 sg682

lemma sg4664 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg374 sg677

lemma sg4665 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg371 sg682

lemma sg4666 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [7,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg684

lemma sg4667 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [7,3,3,2,2] := by
  exact rowSquare_join (by decide) sg372 sg682

lemma sg4668 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [7,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg684

lemma sg4669 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [7,4,4,1,1] := by
  exact rowSquare_join (by decide) sg372 sg684

lemma sg4670 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [7,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg686

lemma sg4671 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [7,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg686

lemma sg4672 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [7,6,2,1,1] := by
  exact rowSquare_join (by decide) sg372 sg686

lemma sg4673 : RowSquare [4,4,2,1,1,1,1,1,1,1] [3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg1032

lemma sg4674 : RowSquare [4,4,2,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg330 sg673

lemma sg4675 : RowSquare [4,4,2,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg676

lemma sg4676 : RowSquare [4,4,2,1,1,1,1,1,1,1] [4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg370 sg616

lemma sg4677 : RowSquare [4,4,2,1,1,1,1,1,1,1] [4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg179 sg1032

lemma sg4678 : RowSquare [4,4,2,1,1,1,1,1,1,1] [4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg179 sg1033

lemma sg4679 : RowSquare [4,4,2,1,1,1,1,1,1,1] [4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg180 sg1033

lemma sg4680 : RowSquare [4,4,2,1,1,1,1,1,1,1] [4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg1041

lemma sg4681 : RowSquare [4,4,2,1,1,1,1,1,1,1] [4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg372 sg615

lemma sg4682 : RowSquare [4,4,2,1,1,1,1,1,1,1] [4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg373 sg615

lemma sg4683 : RowSquare [4,4,2,1,1,1,1,1,1,1] [4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg372 sg616

lemma sg4684 : RowSquare [4,4,2,1,1,1,1,1,1,1] [4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg373 sg616

lemma sg4685 : RowSquare [4,4,2,1,1,1,1,1,1,1] [5,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg330 sg677

lemma sg4686 : RowSquare [4,4,2,1,1,1,1,1,1,1] [5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg370 sg617

lemma sg4687 : RowSquare [4,4,2,1,1,1,1,1,1,1] [5,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg678

lemma sg4688 : RowSquare [4,4,2,1,1,1,1,1,1,1] [5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg370 sg618

lemma sg4689 : RowSquare [4,4,2,1,1,1,1,1,1,1] [5,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg679

lemma sg4690 : RowSquare [4,4,2,1,1,1,1,1,1,1] [5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg374 sg615

lemma sg4691 : RowSquare [4,4,2,1,1,1,1,1,1,1] [5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg376 sg615

lemma sg4692 : RowSquare [4,4,2,1,1,1,1,1,1,1] [5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg372 sg623

lemma sg4693 : RowSquare [4,4,2,1,1,1,1,1,1,1] [6,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg685

lemma sg4694 : RowSquare [4,4,2,1,1,1,1,1,1,1] [6,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg374 sg623

lemma sg4695 : RowSquare [4,4,2,1,1,1,1,1,1,1] [6,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg686

lemma sg4696 : RowSquare [4,4,2,2,1,1,1,1,1] [3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg330 sg613

lemma sg4697 : RowSquare [4,4,2,2,1,1,1,1,1] [6,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg1650

lemma sg4698 : RowSquare [4,4,2,2,1,1,1,1,1] [7,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg1651

lemma sg4699 : RowSquare [4,4,2,2,2,2,1] [4,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg1650

lemma sg4700 : RowSquare [4,4,2,2,2,2,1] [4,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg1650

lemma sg4701 : RowSquare [4,4,2,2,2,2,1] [5,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg1650

lemma sg4702 : RowSquare [4,4,2,2,2,2,1] [5,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg1651

lemma sg4703 : RowSquare [4,4,2,2,2,2,1] [5,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg1651

lemma sg4704 : RowSquare [4,4,2,2,2,2,1] [5,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg1655

lemma sg4705 : RowSquare [4,4,2,2,2,2,1] [5,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg1656

lemma sg4706 : RowSquare [4,4,2,2,2,2,1] [5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg1653

lemma sg4707 : RowSquare [4,4,2,2,2,2,1] [5,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg1652

lemma sg4708 : RowSquare [4,4,2,2,2,2,1] [5,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg1656

lemma sg4709 : RowSquare [4,4,2,2,2,2,1] [6,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg1650

lemma sg4710 : RowSquare [4,4,2,2,2,2,1] [6,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg1651

lemma sg4711 : RowSquare [4,4,2,2,2,2,1] [6,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg1655

lemma sg4712 : RowSquare [4,4,2,2,2,2,1] [6,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg1655

lemma sg4713 : RowSquare [4,4,2,2,2,2,1] [6,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg1657

lemma sg4714 : RowSquare [4,4,2,2,2,2,1] [6,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg1656

lemma sg4715 : RowSquare [4,4,2,2,2,2,1] [7,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg1651

lemma sg4716 : RowSquare [4,4,2,2,2,2,1] [7,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg1655

lemma sg4717 : RowSquare [4,4,2,2,2,2,1] [8,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg1655

lemma sg4718 : RowSquare [4,4,3,2,1,1,1,1] [2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg849

lemma sg4719 : RowSquare [4,4,3,2,1,1,1,1] [5,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg2107

lemma sg4720 : RowSquare [4,4,3,2,1,1,1,1] [6,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg2108

lemma sg4721 : RowSquare [4,4,3,2,1,1,1,1] [6,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg2109

lemma sg4722 : RowSquare [4,4,3,2,1,1,1,1] [7,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg2112

lemma sg4723 : RowSquare [4,4,3,2,1,1,1,1] [7,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3 sg2504

lemma sg4724 : RowSquare [5,3,2,1,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg390 sg586

lemma sg4725 : RowSquare [5,3,2,1,1,1,1,1,1,1] [4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg391 sg586

lemma sg4726 : RowSquare [5,3,2,1,1,1,1,1,1,1] [4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg220 sg910

lemma sg4727 : RowSquare [5,3,2,1,1,1,1,1,1,1] [4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg394 sg586

lemma sg4728 : RowSquare [5,3,2,1,1,1,1,1,1,1] [6,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg1682

lemma sg4729 : RowSquare [5,3,2,2,1,1,1,1,1] [4,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg45 sg1682

lemma sg4730 : RowSquare [5,3,2,2,1,1,1,1,1] [4,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg1682

lemma sg4731 : RowSquare [5,3,2,2,1,1,1,1,1] [5,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg47 sg1682

lemma sg4732 : RowSquare [5,3,2,2,1,1,1,1,1] [5,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg45 sg1683

lemma sg4733 : RowSquare [5,3,2,2,1,1,1,1,1] [5,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg1683

lemma sg4734 : RowSquare [5,3,3,2,1,1,1,1] [2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1682

lemma sg4735 : RowSquare [5,3,3,2,1,1,1,1] [3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg2137

lemma sg4736 : RowSquare [5,3,3,2,1,1,1,1] [3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg33 sg1682

lemma sg4737 : RowSquare [5,3,3,2,1,1,1,1] [3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1683

lemma sg4738 : RowSquare [5,3,3,2,1,1,1,1] [4,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg2137

lemma sg4739 : RowSquare [5,3,3,2,1,1,1,1] [8,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg3865

lemma sg4740 : RowSquare [5,4,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg370 sg586

lemma sg4741 : RowSquare [5,4,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg586

lemma sg4742 : RowSquare [5,4,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg998

lemma sg4743 : RowSquare [5,4,1,1,1,1,1,1,1,1] [3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg372 sg586

lemma sg4744 : RowSquare [5,4,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg999

lemma sg4745 : RowSquare [5,4,1,1,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg373 sg586

lemma sg4746 : RowSquare [5,4,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg1000

lemma sg4747 : RowSquare [5,4,1,1,1,1,1,1,1,1] [3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg178 sg1001

lemma sg4748 : RowSquare [5,4,1,1,1,1,1,1,1,1] [4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg179 sg1000

lemma sg4749 : RowSquare [5,4,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg371 sg588

lemma sg4750 : RowSquare [5,4,1,1,1,1,1,1,1,1] [4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg371 sg589

lemma sg4751 : RowSquare [5,4,1,1,1,1,1,1,1,1] [4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg180 sg1001

lemma sg4752 : RowSquare [5,4,1,1,1,1,1,1,1,1] [4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg373 sg589

lemma sg4753 : RowSquare [5,4,1,1,1,1,1,1,1,1] [4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg373 sg590

lemma sg4754 : RowSquare [5,4,1,1,1,1,1,1,1,1] [5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg376 sg589

lemma sg4755 : RowSquare [5,4,1,1,1,1,1,1,1,1] [6,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg384 sg586

lemma sg4756 : RowSquare [5,4,1,1,1,1,1,1,1,1] [6,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg379 sg587

lemma sg4757 : RowSquare [5,4,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg3876

lemma sg4758 : RowSquare [5,4,1,1,1,1,1,1,1,1] [6,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg385 sg586

lemma sg4759 : RowSquare [5,4,1,1,1,1,1,1,1,1] [6,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg380 sg587

lemma sg4760 : RowSquare [5,4,1,1,1,1,1,1,1,1] [6,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg3877

lemma sg4761 : RowSquare [5,4,1,1,1,1,1,1,1,1] [6,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg3878

lemma sg4762 : RowSquare [5,4,1,1,1,1,1,1,1,1] [6,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg381 sg587

lemma sg4763 : RowSquare [5,4,1,1,1,1,1,1,1,1] [6,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg3879

lemma sg4764 : RowSquare [5,4,1,1,1,1,1,1,1,1] [6,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg3880

lemma sg4765 : RowSquare [5,4,1,1,1,1,1,1,1,1] [6,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg3881

lemma sg4766 : RowSquare [5,4,1,1,1,1,1,1,1,1] [6,3,3,3,2] := by
  exact rowSquare_join (by decide) sg379 sg590

lemma sg4767 : RowSquare [5,4,1,1,1,1,1,1,1,1] [6,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg386 sg586

lemma sg4768 : RowSquare [5,4,1,1,1,1,1,1,1,1] [6,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg383 sg587

lemma sg4769 : RowSquare [5,4,1,1,1,1,1,1,1,1] [7,5,5] := by
  exact rowSquare_join (by decide) sg4 sg2497

lemma sg4770 : RowSquare [5,4,1,1,1,1,1,1,1,1] [9,8] := by
  exact rowSquare_join (by decide) sg0 sg3905

lemma sg4771 : RowSquare [5,4,1,1,1,1,1,1,1,1] [10,7] := by
  exact rowSquare_join (by decide) sg14 sg2020

lemma sg4772 : RowSquare [5,4,1,1,1,1,1,1,1,1] [11,6] := by
  exact rowSquare_join (by decide) sg42 sg1577

lemma sg4773 : RowSquare [5,4,1,1,1,1,1,1,1,1] [12,5] := by
  exact rowSquare_join (by decide) sg42 sg1578

lemma sg4774 : RowSquare [5,4,1,1,1,1,1,1,1,1] [13,4] := by
  exact rowSquare_join (by decide) sg85 sg1120

lemma sg4775 : RowSquare [5,4,1,1,1,1,1,1,1,1] [14,3] := by
  exact rowSquare_join (by decide) sg213 sg718

lemma sg4776 : RowSquare [5,4,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg910

lemma sg4777 : RowSquare [5,4,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg330 sg586

lemma sg4778 : RowSquare [5,4,2,1,1,1,1,1,1] [3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg910

lemma sg4779 : RowSquare [5,4,2,1,1,1,1,1,1] [3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg330 sg587

lemma sg4780 : RowSquare [5,4,2,1,1,1,1,1,1] [3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg180 sg910

lemma sg4781 : RowSquare [5,4,2,1,1,1,1,1,1] [3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg181 sg910

lemma sg4782 : RowSquare [5,4,2,1,1,1,1,1,1] [3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg913

lemma sg4783 : RowSquare [5,4,2,1,1,1,1,1,1] [4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg180 sg915

lemma sg4784 : RowSquare [5,4,2,2,1,1,1,1] [3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg142 sg910

lemma sg4785 : RowSquare [5,4,2,2,1,1,1,1] [3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg143 sg910

lemma sg4786 : RowSquare [5,4,2,2,1,1,1,1] [3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg144 sg910

lemma sg4787 : RowSquare [5,4,2,2,1,1,1,1] [4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg2596

lemma sg4788 : RowSquare [5,4,2,2,1,1,1,1] [4,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg148 sg910

lemma sg4789 : RowSquare [5,4,2,2,1,1,1,1] [4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg543

lemma sg4790 : RowSquare [5,4,2,2,1,1,1,1] [5,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg2597

lemma sg4791 : RowSquare [5,4,2,2,1,1,1,1] [5,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg2598

lemma sg4792 : RowSquare [5,4,2,2,1,1,1,1] [5,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg2599

lemma sg4793 : RowSquare [5,4,2,2,1,1,1,1] [6,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg3935

lemma sg4794 : RowSquare [5,4,2,2,1,1,1,1] [6,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg2603

lemma sg4795 : RowSquare [5,4,2,2,1,1,1,1] [7,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg3936

lemma sg4796 : RowSquare [5,4,2,2,1,1,1,1] [7,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg3199

lemma sg4797 : RowSquare [5,4,2,2,2,1,1] [4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg2596

lemma sg4798 : RowSquare [5,4,2,2,2,1,1] [4,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg2597

lemma sg4799 : RowSquare [5,4,2,2,2,1,1] [4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg2601

lemma sg4800 : RowSquare [5,4,2,2,2,1,1] [4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg2602

lemma sg4801 : RowSquare [5,4,2,2,2,1,1] [5,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg2597

lemma sg4802 : RowSquare [5,4,2,2,2,1,1] [5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg2601

lemma sg4803 : RowSquare [5,4,2,2,2,1,1] [5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6 sg2602

lemma sg4805 : RowSquare [5,5,1,1,1,1,1,1,1] [3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg313 sg586

lemma sg4806 : RowSquare [5,5,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg312 sg587

lemma sg4807 : RowSquare [5,5,1,1,1,1,1,1,1] [4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg313 sg589

lemma sg4808 : RowSquare [5,5,1,1,1,1,1,1,1] [6,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg3211

lemma sg4809 : RowSquare [5,5,1,1,1,1,1,1,1] [6,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg3213

lemma sg4810 : RowSquare [5,5,1,1,1,1,1,1,1] [8,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg2028

lemma sg4811 : RowSquare [5,5,1,1,1,1,1,1,1] [8,5,2,2] := by
  exact rowSquare_join (by decide) sg13 sg2029

lemma sg4812 : RowSquare [5,5,1,1,1,1,1,1,1] [8,5,3,1] := by
  exact rowSquare_join (by decide) sg13 sg2030

lemma sg4813 : RowSquare [5,5,1,1,1,1,1,1,1] [9,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg2032

lemma sg4814 : RowSquare [5,5,1,1,1,1,1,1,1] [9,8] := by
  exact rowSquare_join (by decide) sg14 sg2031

lemma sg4815 : RowSquare [5,5,1,1,1,1,1,1,1] [10,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg2034

lemma sg4816 : RowSquare [5,5,1,1,1,1,1,1,1] [10,3,3,1] := by
  exact rowSquare_join (by decide) sg84 sg1121

lemma sg4817 : RowSquare [5,5,1,1,1,1,1,1,1] [10,7] := by
  exact rowSquare_join (by decide) sg14 sg2033

lemma sg4818 : RowSquare [5,5,1,1,1,1,1,1,1] [11,6] := by
  exact rowSquare_join (by decide) sg85 sg1122

lemma sg4819 : RowSquare [5,5,1,1,1,1,1,1,1] [12,5] := by
  exact rowSquare_join (by decide) sg85 sg1124

lemma sg4820 : RowSquare [5,5,1,1,1,1,1,1,1] [13,4] := by
  exact rowSquare_join (by decide) sg367 sg427

lemma sg4821 : RowSquare [5,5,1,1,1,1,1,1,1] [14,3] := by
  exact rowSquare_join (by decide) sg85 sg1126

lemma sg4822 : RowSquare [5,5,2,1,1,1,1,1] [4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg132 sg910

lemma sg4823 : RowSquare [5,5,2,1,1,1,1,1] [4,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg133 sg910

lemma sg4824 : RowSquare [5,5,2,1,1,1,1,1] [4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg134 sg910

lemma sg4825 : RowSquare [5,5,2,1,1,1,1,1] [4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg275 sg586

lemma sg4826 : RowSquare [5,5,2,1,1,1,1,1] [4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg276 sg586

lemma sg4827 : RowSquare [5,5,2,1,1,1,1,1] [5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg279 sg586

lemma sg4828 : RowSquare [5,5,2,1,1,1,1,1] [5,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg137 sg910

lemma sg4829 : RowSquare [5,5,2,1,1,1,1,1] [5,4,4,4] := by
  exact rowSquare_join (by decide) sg13 sg2035

lemma sg4830 : RowSquare [5,5,2,1,1,1,1,1] [5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg281 sg586

lemma sg4831 : RowSquare [5,5,2,1,1,1,1,1] [5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg314 sg543

lemma sg4833 : RowSquare [5,5,3,2,2] [2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg253 sg509

lemma sg4834 : RowSquare [6,3,2,1,1,1,1,1,1] [2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1754

lemma sg4835 : RowSquare [6,3,2,1,1,1,1,1,1] [2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg1327

lemma sg4836 : RowSquare [6,3,2,1,1,1,1,1,1] [3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg1328

lemma sg4837 : RowSquare [6,3,2,1,1,1,1,1,1] [3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1755

lemma sg4838 : RowSquare [6,3,2,1,1,1,1,1,1] [3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg1329

lemma sg4839 : RowSquare [6,3,2,1,1,1,1,1,1] [3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1757

lemma sg4840 : RowSquare [6,3,2,1,1,1,1,1,1] [3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg1331

lemma sg4841 : RowSquare [6,3,2,1,1,1,1,1,1] [3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1758

lemma sg4842 : RowSquare [6,3,2,1,1,1,1,1,1] [3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg74 sg1332

lemma sg4843 : RowSquare [6,3,2,1,1,1,1,1,1] [4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg1338

lemma sg4844 : RowSquare [6,3,2,2,2,2] [4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg166 sg762

lemma sg4845 : RowSquare [6,4,1,1,1,1,1,1,1] [3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg66 sg1327

lemma sg4846 : RowSquare [6,4,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg889

lemma sg4847 : RowSquare [6,4,1,1,1,1,1,1,1] [3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg890

lemma sg4848 : RowSquare [6,4,1,1,1,1,1,1,1] [3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg178 sg892

lemma sg4849 : RowSquare [6,4,2,1,1,1,1,1] [4,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg22 sg1754

lemma sg4850 : RowSquare [6,4,2,1,1,1,1,1] [4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg56 sg1327

lemma sg4851 : RowSquare [6,4,2,1,1,1,1,1] [4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg3259

lemma sg4852 : RowSquare [6,4,2,1,1,1,1,1] [4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg3232

lemma sg4853 : RowSquare [6,4,2,1,1,1,1,1] [4,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg3983

lemma sg4854 : RowSquare [6,4,2,1,1,1,1,1] [4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg3984

lemma sg4855 : RowSquare [6,4,2,1,1,1,1,1] [5,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg24 sg1754

lemma sg4856 : RowSquare [6,4,2,1,1,1,1,1] [5,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg3261

lemma sg4857 : RowSquare [6,4,2,1,1,1,1,1] [6,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg3266

lemma sg4858 : RowSquare [6,4,2,1,1,1,1,1] [6,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg60 sg1327

lemma sg4859 : RowSquare [6,4,2,1,1,1,1,1] [6,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg2534

lemma sg4860 : RowSquare [6,4,2,1,1,1,1,1] [6,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg3267

lemma sg4861 : RowSquare [6,4,3,1,1,1,1] [3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1628

lemma sg4863 : RowSquare [6,4,3,2,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg347 sg445

lemma sg4864 : RowSquare [6,4,3,2,1,1] [2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg346 sg445

lemma sg4865 : RowSquare [6,4,3,2,1,1] [2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg345 sg445

lemma sg4866 : RowSquare [6,4,3,2,1,1] [2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg342 sg445

lemma sg4867 : RowSquare [6,4,3,2,1,1] [2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg342 sg444

lemma sg4868 : RowSquare [6,4,3,2,1,1] [2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg342 sg443

lemma sg4869 : RowSquare [6,4,3,2,1,1] [2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg342 sg442

lemma sg4870 : RowSquare [6,4,3,2,1,1] [3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg2545

lemma sg4871 : RowSquare [6,4,3,2,1,1] [3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg340 sg440

lemma sg4872 : RowSquare [6,4,3,2,1,1] [3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg32 sg1616

lemma sg4873 : RowSquare [6,5,1,1,1,1,1,1] [5,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg51 sg1327

lemma sg4874 : RowSquare [6,5,1,1,1,1,1,1] [5,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg52 sg1327

lemma sg4875 : RowSquare [7,3,3,1,1,1,1] [2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg355 sg454

lemma sg4876 : RowSquare [7,3,3,1,1,1,1] [2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg354 sg453

lemma sg4877 : RowSquare [7,3,3,1,1,1,1] [2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg354 sg451

lemma sg4878 : RowSquare [7,3,3,1,1,1,1] [2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg92 sg1143

lemma sg4879 : RowSquare [7,3,3,1,1,1,1] [3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg89 sg1142

lemma sg4880 : RowSquare [7,4,3,1,1,1] [4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg77 sg1195

lemma sg4881 : RowSquare [7,4,3,1,1,1] [4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg32 sg1587

lemma sg4882 : RowSquare [7,4,3,2,1] [3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg790

lemma sg4883 : RowSquare [7,4,3,2,1] [3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg178 sg792

lemma sg4884 : RowSquare [7,4,3,2,1] [4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg795

lemma sg4885 : RowSquare [7,4,3,2,1] [4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg334 sg476

lemma sg4886 : RowSquare [7,4,3,3] [3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg330 sg480

lemma sg4887 : RowSquare [7,4,3,3] [4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg334 sg481

lemma sg4888 : RowSquare [7,5,1,1,1,1,1] [5,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg2128

lemma sg4889 : RowSquare [7,5,3,1,1] [3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg306 sg534

lemma sg4890 : RowSquare [8,3,1,1,1,1,1,1] [4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg2620

lemma sg4891 : RowSquare [8,3,1,1,1,1,1,1] [6,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg2116

lemma sg4892 : RowSquare [8,3,1,1,1,1,1,1] [6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg2117

lemma sg4893 : RowSquare [8,3,1,1,1,1,1,1] [6,6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg2118

lemma sg4894 : RowSquare [8,3,2,1,1,1,1] [4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1666

lemma sg4895 : RowSquare [8,3,2,1,1,1,1] [4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg1667

lemma sg4896 : RowSquare [8,3,2,2,1,1] [4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg2529

lemma sg4897 : RowSquare [8,3,3,1,1,1] [3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg62 sg1327

lemma sg4898 : RowSquare [8,3,3,2,1] [3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg286 sg586

lemma sg4899 : RowSquare [8,3,3,2,1] [4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg179 sg828

lemma sg4900 : RowSquare [8,4,1,1,1,1,1] [4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg2159

lemma sg4901 : RowSquare [8,4,1,1,1,1,1] [4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg13 sg2160

lemma sg4902 : RowSquare [8,4,1,1,1,1,1] [5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg2161

lemma sg4903 : RowSquare [8,4,1,1,1,1,1] [5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg2162

lemma sg4904 : RowSquare [8,4,1,1,1,1,1] [5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg2163

lemma sg4905 : RowSquare [8,4,1,1,1,1,1] [5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg2164

lemma sg4906 : RowSquare [8,4,1,1,1,1,1] [5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg1185

lemma sg4907 : RowSquare [8,4,1,1,1,1,1] [5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg2122

lemma sg4908 : RowSquare [8,4,1,1,1,1,1] [5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg17 sg2123

lemma sg4909 : RowSquare [8,4,1,1,1,1,1] [5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg1188

lemma sg4910 : RowSquare [8,4,1,1,1,1,1] [5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg2165

lemma sg4911 : RowSquare [8,4,1,1,1,1,1] [5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg17 sg2125

lemma sg4912 : RowSquare [8,4,1,1,1,1,1] [5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg1189

lemma sg4913 : RowSquare [8,4,1,1,1,1,1] [6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg2130

lemma sg4914 : RowSquare [8,4,1,1,1,1,1] [6,6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg1670

lemma sg4915 : RowSquare [8,4,1,1,1,1,1] [6,6,2,2,1] := by
  exact rowSquare_join (by decide) sg17 sg2131

lemma sg4916 : RowSquare [8,4,1,1,1,1,1] [7,7,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg2133

lemma sg4917 : RowSquare [8,4,3,1,1] [2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1682

lemma sg4918 : RowSquare [8,4,3,1,1] [2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg306 sg586

end UniversalTensorSquare
end
end

end OAI
