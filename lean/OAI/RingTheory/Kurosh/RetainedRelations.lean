import Mathlib
import OAI.RingTheory.Kurosh.ScheduledTowers

namespace OAI

/-! Persistence of formal identities and scheduled polynomial relations. -/

namespace KuroshConstruction

lemma freeScalarChange_aeval {K L I : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (p : FreeAlgebra K I) (q : Polynomial K) :
    freeScalarChange φ (Polynomial.aeval p q) =
      Polynomial.aeval (freeScalarChange φ p) (q.map φ) := by
  apply Polynomial.map_aeval_eq_aeval_map
  ext c
  simp

lemma constant_free_evaluate {K A I : Type*} [CommRing K] [Ring A] [Algebra K A]
    (X : I → FreeSeries A) (p : FreeAlgebra K I) :
    FreeSeries.constantCoeffAlgHom (K := K) (FreeAlgebra.lift K X p) =
      FreeAlgebra.lift K (fun c => (X c).coeff []) p := by
  induction p using FreeAlgebra.induction with
  | grade0 c => simp only [AlgHom.commutes]
  | grade1 i => simp; rfl
  | mul p q hp hq => simp only [map_mul, hp, hq]
  | add p q hp hq => simp only [map_add, hp, hq]

lemma sequence_formal_retained (hL : LiftingStatement) (i n : ℕ) (hin : i ≤ n)
    (p : FreeAlgebra (sequenceStage hL i).K (Fin 2))
    (hp : FreeAlgebra.lift (sequenceStage hL i).K (sequenceStage hL i).X p = 0) :
    FreeAlgebra.lift (sequenceStage hL n).K (sequenceStage hL n).X
      (freeScalarChange (sequenceFieldMap hL i n hin) p) = 0 := by
  induction n, hin using Nat.le_induction with
  | base => simpa only [sequenceFieldMap_self, freeScalarChange_id] using hp
  | succ n hn ih =>
    have hh := (sequenceStep hL n).identities _ ih
    rwa [freeScalarChange_comp, ← sequenceFieldMap_succ] at hh

lemma sequence_polynomial_retained (hL : LiftingStatement) (i n : ℕ) (hin : i ≤ n)
    (p : FreeAlgebra (sequenceStage hL i).K (Fin 2))
    (q : Polynomial (sequenceStage hL i).K)
    (hq : Polynomial.aeval
      (FreeAlgebra.lift (sequenceStage hL i).K (sequenceStage hL i).X p) q = 0) :
    Polynomial.aeval
      (FreeAlgebra.lift (sequenceStage hL n).K (sequenceStage hL n).X
        (freeScalarChange (sequenceFieldMap hL i n hin) p))
      (q.map (sequenceFieldMap hL i n hin)) = 0 := by
  have hp : FreeAlgebra.lift (sequenceStage hL i).K (sequenceStage hL i).X
      (Polynomial.aeval p q) = 0 := by
    rwa [← Polynomial.aeval_algHom_apply]
  have hh := sequence_formal_retained hL i n hin (Polynomial.aeval p q) hp
  rw [freeScalarChange_aeval, ← Polynomial.aeval_algHom_apply] at hh
  exact hh

theorem sequence_scheduled_formal (hL : LiftingStatement) (i : ℕ)
    (p : FreeAlgebra (sequenceStage hL i).K (Fin 2)) :
    ∃ m, ∃ him : i ≤ m, ∃ q : Polynomial (sequenceStage hL m).K,
      q.Monic ∧ ∀ n (hmn : m ≤ n), Polynomial.aeval
        (FreeAlgebra.lift (sequenceStage hL n).K (sequenceStage hL n).X
          (freeScalarChange (sequenceFieldMap hL i n (him.trans hmn)) p))
        (q.map (sequenceFieldMap hL m n hmn)) = 0 := by
  obtain ⟨j, hj⟩ := stageEnumeration_surjective (sequenceStage hL i) p
  let k := Nat.pair i j
  have hik : i ≤ k := Nat.left_le_pair i j
  have ht : (scheduledSequence hL k).task (Nat.unpair k).1 (Nat.unpair k).2 =
      freeScalarChange (sequenceFieldMap hL i k hik) p := by
    simp only [k, Nat.unpair_pair]
    rw [sequence_task_transport hL i (Nat.pair i j) hik j, hj]
  have hInt := (sequenceStep hL k).integral
  simp only [ht] at hInt
  rw [freeScalarChange_comp, ← sequenceFieldMap_succ] at hInt
  obtain ⟨q, hq, he⟩ := hInt
  refine ⟨k+1, hik.trans (Nat.le_succ k), q, hq, ?_⟩
  intro n hkn
  have hh := sequence_polynomial_retained hL (k+1) n hkn
    (freeScalarChange (sequenceFieldMap hL i (k+1) (hik.trans (Nat.le_succ k))) p) q he
  rwa [freeScalarChange_comp, ← sequenceFieldMap_trans] at hh

lemma sequence_scheduled_constants (hL : LiftingStatement) (i : ℕ)
    (p : FreeAlgebra (sequenceStage hL i).K (Fin 2)) :
    ∃ m, ∃ him : i ≤ m, ∃ q : Polynomial (sequenceStage hL m).K,
      q.Monic ∧ ∀ n (hmn : m ≤ n), Polynomial.aeval
        (FreeAlgebra.lift (sequenceStage hL n).K (constantTuple (sequenceStage hL n).X)
          (freeScalarChange (sequenceFieldMap hL i n (him.trans hmn)) p))
        (q.map (sequenceFieldMap hL m n hmn)) = 0 := by
  obtain ⟨m, him, q, hq, he⟩ := sequence_scheduled_formal hL i p
  refine ⟨m, him, q, hq, fun n hmn => ?_⟩
  have hh := congrArg (FreeSeries.constantCoeffAlgHom (K := (sequenceStage hL n).K))
    (he n hmn)
  rw [map_zero, ← Polynomial.aeval_algHom_apply, constant_free_evaluate] at hh
  exact hh

end KuroshConstruction

end OAI
