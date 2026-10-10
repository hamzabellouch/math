import Mathlib
import OAI.RingTheory.Kurosh.LimitEvaluation

namespace OAI

/-! Asymptotic linear independence in a division-ring ultraproduct. -/

namespace KuroshConstruction

open Filter

open scoped BigOperators

section AsymptoticIndependence

variable (U : Ultrafilter ℕ) [hU : Fact ((U : Filter ℕ) ≤ atTop)]
  (K A : ℕ → Type*) [∀ i, Field (K i)] [∀ i, DivisionRing (A i)]
  [∀ i, Algebra (K i) (A i)]
  (f : ∀ i j, i ≤ j → K i →+* K j)
  [DirectedSystem K (fun i j h => f i j h)]

theorem ultra_linearIndependent {J : Type*} [Fintype J] (v : J → ∀ i, A i)
    (hv : ∀ᶠ i in U, LinearIndependent (K i) (fun j => v j i)) :
    LinearIndependent (DirectLimit K f) (fun j => ultraMap U A (v j)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  obtain ⟨n, a, ha⟩ := limit_finite_tuple K f c
  have he : ultraMap U A (∑ k, tailCoefficients K A f n (a k) * v k) = 0 := by
    rw [map_sum]
    convert hc using 1
    apply Finset.sum_congr rfl
    intro k _
    rw [map_mul, ← ha k, Algebra.smul_def]
    rfl
  rw [← map_zero (ultraMap U A)] at he
  have hei := (ultraMap_eq_iff U A _ _).mp he
  obtain ⟨i, hi, hvi, hn⟩ :=
    (hei.and (hv.and ((eventually_ge_atTop n).filter_mono hU.out))).exists
  have hr : ∑ k, f n i hn (a k) • v k i = 0 := by
    simpa only [Finset.sum_apply, Pi.mul_apply, tailCoefficients, dite_eq_left hn,
      Pi.zero_apply, Algebra.smul_def] using hi
  have haz := (Fintype.linearIndependent_iff.mp hvi) _ hr j
  have haj : a j = 0 := (f n i hn).injective (by simpa using haz)
  rw [← ha j, haj, map_zero]

end AsymptoticIndependence

end KuroshConstruction

end OAI
