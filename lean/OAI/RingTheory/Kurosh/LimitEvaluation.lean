import Mathlib
import OAI.RingTheory.Kurosh.LimitScalars
import OAI.RingTheory.Kurosh.RetainedRelations

namespace OAI

/-! Evaluation of free polynomials in the ultraproduct. -/

namespace KuroshConstruction

open Filter

section TailPolynomial

variable (U : Ultrafilter ℕ) [hU : Fact ((U : Filter ℕ) ≤ atTop)]
  (K A : ℕ → Type*) [∀ i, Field (K i)] [∀ i, DivisionRing (A i)]
  [∀ i, Algebra (K i) (A i)]
  (f : ∀ i j, i ≤ j → K i →+* K j)
  [DirectedSystem K (fun i j h => f i j h)]

noncomputable instance ultraLimitAlgebraInst :
    Algebra (DirectLimit K f) (DivisionUltraproduct U A) :=
  ultraLimitAlgebra U hU.out K A f

variable {I : Type*}

noncomputable def tailFreeValue (X : I → ∀ i, A i) (j : ℕ)
    (p : FreeAlgebra (K j) I) : ∀ i, A i := fun i =>
  if h : j ≤ i then
    FreeAlgebra.lift (K i) (fun c => X c i) (freeScalarChange (f j i h) p)
  else 0

omit [DirectedSystem K (fun i j h => f i j h)] in
noncomputable def ultraTailFreeEval (X : I → ∀ i, A i) (j : ℕ) :
    FreeAlgebra (K j) I →+* DivisionUltraproduct U A where
  toFun p := ultraMap U A (tailFreeValue K A f X j p)
  map_one' := by
    rw [← map_one (ultraMap U A)]
    apply (ultraMap_eq_iff U A _ _).mpr
    exact ((eventually_ge_atTop j).filter_mono hU.out).mono (fun i hi => by
      simp [tailFreeValue, hi])
  map_zero' := by
    rw [← map_zero (ultraMap U A)]
    apply (ultraMap_eq_iff U A _ _).mpr
    exact Eventually.of_forall (fun i => by simp [tailFreeValue])
  map_mul' p q := by
    rw [← map_mul]
    apply (ultraMap_eq_iff U A _ _).mpr
    exact ((eventually_ge_atTop j).filter_mono hU.out).mono (fun i hi => by
      simp [tailFreeValue, hi])
  map_add' p q := by
    rw [← map_add]
    apply (ultraMap_eq_iff U A _ _).mpr
    exact ((eventually_ge_atTop j).filter_mono hU.out).mono (fun i hi => by
      simp [tailFreeValue, hi])

lemma ultraFree_evaluate (X : I → ∀ i, A i) (j : ℕ) (p : FreeAlgebra (K j) I) :
    FreeAlgebra.lift (DirectLimit K f) (fun c => ultraMap U A (X c))
      (freeScalarChange (DirectLimit.Ring.of K f j) p) =
    ultraTailFreeEval U K A f X j p := by
  induction p using FreeAlgebra.induction with
  | grade0 c =>
    rw [freeScalarChange_algebraMap, AlgHom.commutes]
    change ultraMap U A (tailCoefficients K A f j c) =
      ultraMap U A (tailFreeValue K A f X j (algebraMap _ _ c))
    apply (ultraMap_eq_iff U A _ _).mpr
    exact Eventually.of_forall (fun i => by
      simp [tailCoefficients, tailFreeValue])
  | grade1 c =>
    rw [freeScalarChange_ι, FreeAlgebra.lift_ι_apply]
    apply (ultraMap_eq_iff U A _ _).mpr
    exact ((eventually_ge_atTop j).filter_mono hU.out).mono (fun i hi => by
      simp [tailFreeValue, hi])
  | mul p q hp hq => simp only [map_mul, hp, hq]
  | add p q hp hq => simp only [map_add, hp, hq]

noncomputable def tailPolynomialValue (m : ℕ) (q : Polynomial (K m))
    (v : ∀ i, A i) : ∀ i, A i := fun i =>
  if h : m ≤ i then Polynomial.aeval (v i) (q.map (f m i h)) else 0

lemma ultraPolynomial_evaluate (m : ℕ) (q : Polynomial (K m)) (v : ∀ i, A i) :
    Polynomial.aeval (R := DirectLimit K f) (ultraMap U A v)
      (q.map (DirectLimit.Ring.of K f m)) =
      ultraMap U A (tailPolynomialValue K A f m q v) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.map_add, map_add, hp, hq, ← map_add]
    apply (ultraMap_eq_iff U A _ _).mpr
    exact Eventually.of_forall (fun i => by
      by_cases hi : m ≤ i <;> simp [tailPolynomialValue, hi])
  | monomial n c =>
    rw [Polynomial.map_monomial, Polynomial.aeval_monomial]
    change ultraMap U A (tailCoefficients K A f m c) * (ultraMap U A v)^n = _
    rw [← map_pow, ← map_mul]
    apply (ultraMap_eq_iff U A _ _).mpr
    exact ((eventually_ge_atTop m).filter_mono hU.out).mono (fun i hi => by
      simp [tailCoefficients, tailPolynomialValue, hi])

end TailPolynomial

end KuroshConstruction

end OAI
