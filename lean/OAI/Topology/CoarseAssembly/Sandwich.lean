import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# The operator-norm sandwich estimate

The norm estimate and closure step do not require an amplified
constant-fiber projection to be locally compact.
Membership of the approximating sandwiches in the closed algebra is explicit.
-/

namespace CoarseAssembly

section Estimate

variable {A : Type*} [NormedRing A]

/-- The uniform `2 ‖Q-P‖ ‖T‖` bound for sandwiching by contractions. -/
theorem sandwich_error_bound (P Q T : A) (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) :
    ‖Q * T * Q - P * T * P‖ ≤ 2 * ‖Q - P‖ * ‖T‖ := by
  have hexpand : Q * T * Q - P * T * P = (Q - P) * T * Q + P * T * (Q - P) := by
    noncomm_ring
  rw [hexpand]
  calc
    ‖(Q - P) * T * Q + P * T * (Q - P)‖ ≤
        ‖(Q - P) * T * Q‖ + ‖P * T * (Q - P)‖ := norm_add_le _ _
    _ ≤ ‖Q - P‖ * ‖T‖ * ‖Q‖ + ‖P‖ * ‖T‖ * ‖Q - P‖ := by
      exact add_le_add
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
    _ ≤ 2 * ‖Q - P‖ * ‖T‖ := by
      have hleft := mul_le_mul_of_nonneg_left hQ (mul_nonneg (norm_nonneg (Q-P)) (norm_nonneg T))
      have hright := mul_le_mul_of_nonneg_right hP (mul_nonneg (norm_nonneg T) (norm_nonneg (Q-P)))
      nlinarith

end Estimate

section ClosedRange

variable {A : Type*} [NormedRing A]

/-- Norm convergence of the finite-propagation projections passes their
sandwiches into any norm-closed algebra. The hypothesis concerns the
sandwiches themselves, as required for local compactness in the paper. -/
theorem sandwich_mem_of_tendsto (S : Set A) (hS : IsClosed S) (P : A)
    (Pn : ℕ → A) (hlim : Filter.Tendsto Pn Filter.atTop (nhds P)) (T : A)
    (hmem : ∀ n, Pn n * T * Pn n ∈ S) : P * T * P ∈ S := by
  apply hS.mem_of_tendsto ((hlim.mul tendsto_const_nhds).mul hlim)
  exact Filter.Eventually.of_forall hmem

end ClosedRange

end CoarseAssembly

end OAI
