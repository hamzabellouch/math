import Mathlib
import OAI.RingTheory.Kurosh.ScheduledLimit

namespace OAI

/-! Construction of a Kurosh counterexample under the algebraic lifting proposition. -/

namespace KuroshConstruction

open Filter

theorem lifting_implies_main (hL : LiftingStatement) : MainStatement := by
  let K : ℕ → Type := fun n => (sequenceStage hL n).K
  let A : ℕ → Type := fun n => (sequenceStage hL n).A
  let : ∀ n, Field (K n) := fun n => (sequenceStage hL n).fieldK
  let : ∀ n, DivisionRing (A n) := fun n => (sequenceStage hL n).divisionA
  let : ∀ n, Algebra (K n) (A n) := fun n => (sequenceStage hL n).algebraKA
  let : ∀ n, Module.Finite (K n) (A n) := fun n => (sequenceStage hL n).finiteA
  let : ∀ n, Countable (K n) := fun n => (sequenceStage hL n).countableK
  let : ∀ n, CharZero (K n) := fun n => (sequenceStage hL n).charZeroK
  let : ∀ n, CharZero (A n) := fun n =>
    charZero_of_injective_ringHom (algebraMap (K n) (A n)).injective
  let f : ∀ i j, i ≤ j → K i →+* K j := sequenceFieldMap hL
  let : DirectedSystem K (fun i j h => f i j h) := sequenceDirectedSystem hL
  let X : Fin 2 → ∀ i, A i := fun c i => constantTuple (sequenceStage hL i).X c
  apply scheduled_tower_yields_main K A f X
  · intro n
    exact (sequenceStage hL n).input.1
  · intro n
    apply (eventually_ge_atTop n).mono
    intro i hi
    exact hi.trans ((sequence_degree_growth hL i).trans (Nat.sqrt_le_self _))
  · intro i p
    obtain ⟨m, him, q, hq, he⟩ := sequence_scheduled_constants hL i p
    refine ⟨m, q, hq, (eventually_ge_atTop m).mono ?_⟩
    intro n hmn
    simpa only [tailPolynomialValue, tailFreeValue, dite_eq_left hmn,
      dite_eq_left (him.trans hmn)] using he n hmn

end KuroshConstruction

end OAI
