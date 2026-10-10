import Mathlib
import OAI.RingTheory.Kurosh.TangentDirections

namespace OAI

/-! Countable towers with scheduled algebraicity requirements and growing degree. -/

namespace KuroshConstruction

noncomputable def stageEnumeration (S : LiftingStage) : ℕ → FreeAlgebra S.K (Fin 2) := by
  have : Countable (FreeMonoid (Fin 2)) := inferInstanceAs (Countable (List (Fin 2)))
  have : Countable (MonoidAlgebra S.K (FreeMonoid (Fin 2))) :=
    Function.Injective.countable MonoidAlgebra.coeffEquiv.injective
  have : Countable (FreeAlgebra S.K (Fin 2)) :=
    Function.Injective.countable (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (R := S.K) (X := Fin 2)).injective
  exact Classical.choose (exists_surjective_nat (FreeAlgebra S.K (Fin 2)))

lemma stageEnumeration_surjective (S : LiftingStage) :
    Function.Surjective (stageEnumeration S) := by
  have : Countable (FreeMonoid (Fin 2)) := inferInstanceAs (Countable (List (Fin 2)))
  have : Countable (MonoidAlgebra S.K (FreeMonoid (Fin 2))) :=
    Function.Injective.countable MonoidAlgebra.coeffEquiv.injective
  have : Countable (FreeAlgebra S.K (Fin 2)) :=
    Function.Injective.countable (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (R := S.K) (X := Fin 2)).injective
  exact Classical.choose_spec (exists_surjective_nat (FreeAlgebra S.K (Fin 2)))

structure ScheduledState where
  stage : LiftingStage
  task : ℕ → ℕ → FreeAlgebra stage.K (Fin 2)

noncomputable def initialScheduledState : ScheduledState :=
  ⟨seedStage, fun i => if i = 0 then stageEnumeration seedStage else fun _ => 0⟩

noncomputable def nextScheduledStage (hL : LiftingStatement) (n : ℕ)
    (Q : ScheduledState) : LiftingStage :=
  Classical.choose (lifting_step_exists hL Q.stage
    (Q.task (Nat.unpair n).1 (Nat.unpair n).2))

noncomputable def nextScheduledStep (hL : LiftingStatement) (n : ℕ)
    (Q : ScheduledState) : LiftingStep Q.stage (nextScheduledStage hL n Q)
      (Q.task (Nat.unpair n).1 (Nat.unpair n).2) :=
  Classical.choice (Classical.choose_spec (lifting_step_exists hL Q.stage
    (Q.task (Nat.unpair n).1 (Nat.unpair n).2)))

noncomputable def nextScheduledState (hL : LiftingStatement) (n : ℕ)
    (Q : ScheduledState) : ScheduledState :=
  ⟨nextScheduledStage hL n Q, fun i j => if i = n + 1 then
    stageEnumeration (nextScheduledStage hL n Q) j else
    freeScalarChange (nextScheduledStep hL n Q).scalar (Q.task i j)⟩

noncomputable def scheduledSequence (hL : LiftingStatement) : ℕ → ScheduledState
  | 0 => initialScheduledState
  | n + 1 => nextScheduledState hL n (scheduledSequence hL n)

noncomputable def sequenceStage (hL : LiftingStatement) (n : ℕ) : LiftingStage :=
  (scheduledSequence hL n).stage

noncomputable def sequenceStep (hL : LiftingStatement) (n : ℕ) :
    LiftingStep (sequenceStage hL n) (sequenceStage hL (n+1))
      ((scheduledSequence hL n).task (Nat.unpair n).1 (Nat.unpair n).2) :=
  nextScheduledStep hL n (scheduledSequence hL n)

noncomputable def sequenceFieldMap (hL : LiftingStatement) (i j : ℕ) (h : i ≤ j) :
    (sequenceStage hL i).K →+* (sequenceStage hL j).K :=
  Nat.leRecOn h (fun {n} φ => (sequenceStep hL n).scalar.comp φ) (RingHom.id _)

@[simp] lemma sequenceFieldMap_self (hL : LiftingStatement) (i : ℕ) (h : i ≤ i) :
    sequenceFieldMap hL i i h = RingHom.id _ := by
  unfold sequenceFieldMap
  rw [Nat.leRecOn_self]

lemma sequenceFieldMap_succ (hL : LiftingStatement) (i j : ℕ) (h : i ≤ j) :
    sequenceFieldMap hL i (j+1) (Nat.le.step h) =
      (sequenceStep hL j).scalar.comp (sequenceFieldMap hL i j h) := by
  unfold sequenceFieldMap
  rw [Nat.leRecOn_succ]

lemma sequenceFieldMap_trans (hL : LiftingStatement) (i j k : ℕ)
    (hij : i ≤ j) (hjk : j ≤ k) :
    sequenceFieldMap hL i k (hij.trans hjk) =
      (sequenceFieldMap hL j k hjk).comp (sequenceFieldMap hL i j hij) := by
  induction k, hjk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [sequenceFieldMap_succ hL i k (hij.trans hk), sequenceFieldMap_succ, ih]
    rfl

instance sequenceDirectedSystem (hL : LiftingStatement) :
    DirectedSystem (fun i => (sequenceStage hL i).K)
      (fun i j h => sequenceFieldMap hL i j h) where
  map_self x := by simp
  map_map k j i hij hjk x := by
    rw [← RingHom.comp_apply, ← sequenceFieldMap_trans]

lemma sequence_task_new (hL : LiftingStatement) (i : ℕ) :
    (scheduledSequence hL i).task i = stageEnumeration (sequenceStage hL i) := by
  cases i with
  | zero => rfl
  | succ i =>
    funext j
    simp [scheduledSequence, nextScheduledState, sequenceStage]
    rfl

lemma sequence_task_old (hL : LiftingStatement) (i n : ℕ) (hin : i ≤ n) (j : ℕ) :
    (scheduledSequence hL (n+1)).task i j =
      freeScalarChange (sequenceStep hL n).scalar ((scheduledSequence hL n).task i j) := by
  change (if i = n + 1 then _ else _) = _
  exact ite_eq_right (by omega)

lemma sequence_task_transport (hL : LiftingStatement) (i n : ℕ) (hin : i ≤ n) (j : ℕ) :
    (scheduledSequence hL n).task i j =
      freeScalarChange (sequenceFieldMap hL i n hin) (stageEnumeration (sequenceStage hL i) j) := by
  induction n, hin using Nat.le_induction with
  | base =>
    rw [sequenceFieldMap_self, freeScalarChange_id]
    exact congrFun (sequence_task_new hL i) j
  | succ n hn ih =>
    rw [sequence_task_old hL i n hn j, ih, sequenceFieldMap_succ]
    rw [freeScalarChange_comp]

lemma sequence_degree_growth (hL : LiftingStatement) (n : ℕ) :
    n ≤ Nat.sqrt (Module.finrank (sequenceStage hL n).K (sequenceStage hL n).A) := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (ih.trans_lt (sequenceStep hL n).grow)

end KuroshConstruction

end OAI
