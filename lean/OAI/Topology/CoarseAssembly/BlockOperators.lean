import OAI.Topology.CoarseAssembly.Definitions
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # Uniform block operators on Hilbert sums

The averaging operators used in the transfer act separately on finite
fibers. A uniform norm bound, rather than finiteness of the set of fibers,
makes their direct sum a bounded operator. The resulting operator admits the uniform approximation needed for the
fiber projection.
-/

noncomputable section

namespace CoarseAssembly

open Filter
open scoped Topology

variable {ι : Type*} {E F : ι → Type*}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
variable [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]

theorem blockLinear_norm_le (A : ∀ i, E i →L[ℂ] F i) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i, ‖A i‖ ≤ C) (x : lp E 2) :
    ‖blockLinear A C hC hA x‖ ≤ C * ‖x‖ := by
  calc
    _ ≤ ‖C • lp.toNorm x‖ := by
      apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
      intro i
      change ‖A i (x i)‖ ≤ ‖C * ‖x i‖‖
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC (norm_nonneg _))]
      exact (A i).le_opNorm (x i) |>.trans
        (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))
    _ = C * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC, lp.norm_toNorm]

@[simp] theorem blockOperator_apply (A : ∀ i, E i →L[ℂ] F i) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i, ‖A i‖ ≤ C) (x : lp E 2) (i : ι) :
    blockOperator A C hC hA x i = A i (x i) := rfl

theorem blockOperator_norm_le (A : ∀ i, E i →L[ℂ] F i) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i, ‖A i‖ ≤ C) : ‖blockOperator A C hC hA‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (blockLinear_norm_le A C hC hA)

@[simp] theorem blockIsometry_apply (V : ∀ i, E i →ₗᵢ[ℂ] F i) (x : lp E 2) (i : ι) :
    blockIsometry V x i = V i (x i) := rfl

/-- Uniform fiberwise norm error bounds the operator error on the whole
Hilbert sum. This is the norm estimate for the amplified Kazhdan projection. -/
theorem blockOperator_dist_le (A B : ∀ i, E i →L[ℂ] F i)
    (C D ε : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D)
    (hAB : ∀ i, ‖A i - B i‖ ≤ ε) :
    ‖blockOperator A C hC hA - blockOperator B D hD hB‖ ≤ ε := by
  have heq : blockOperator A C hC hA - blockOperator B D hD hB =
      blockOperator (fun i => A i - B i) ε hε hAB := by
    ext x i
    rfl
  rw [heq]
  exact blockOperator_norm_le _ _ _ _

theorem power_mul_fixed {R : Type*} [Monoid R] (M P : R) (hMP : M * P = P) (n : ℕ) :
    M ^ n * P = P := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_assoc, hMP, ih]

/-- Removing a fixed projection converts averaging powers into powers on
its complementary subspace. This identity needs no spectral theorem. -/
theorem projection_error_power {R : Type*} [Ring R] (M P : R)
    (hPP : P * P = P) (hMP : M * P = P) (hPM : P * M = P) (n : ℕ) :
    (M - P) ^ (n + 1) = M ^ (n + 1) - P := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (M - P), ih, mul_sub, sub_mul, sub_mul,
      power_mul_fixed M P hMP, hPM, hPP, sub_self, sub_zero, ← pow_succ]

theorem averaging_power_norm_le (M : ∀ i, E i →L[ℂ] E i)
    (hM : ∀ i, ‖M i‖ ≤ 1) (n : ℕ) (i : ι) : ‖M i ^ (n + 1)‖ ≤ 1 := by
  calc
    _ ≤ ‖M i‖ ^ (n + 1) := norm_pow_le' _ (Nat.succ_pos n)
    _ ≤ 1 ^ (n + 1) := by gcongr; exact hM i
    _ = 1 := one_pow _

/-- The uniform spectral-gap consequence needed by the transfer. The
published input is the strict contraction bound on `M i - P i`; norm
convergence of the direct sum is proved here. -/
theorem averaging_blocks_tendsto (M P : ∀ i, E i →L[ℂ] E i)
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c < 1)
    (hM : ∀ i, ‖M i‖ ≤ 1) (hP : ∀ i, ‖P i‖ ≤ 1)
    (hPP : ∀ i, P i * P i = P i) (hMP : ∀ i, M i * P i = P i)
    (hPM : ∀ i, P i * M i = P i) (hgap : ∀ i, ‖M i - P i‖ ≤ c) :
    Tendsto
      (fun n : ℕ => blockOperator (fun i => M i ^ (n + 1)) 1 (by norm_num)
        (averaging_power_norm_le M hM n))
      atTop (nhds (blockOperator P 1 (by norm_num) hP)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (show Tendsto (fun n : ℕ => c ^ (n + 1)) atTop (nhds 0) by
      simpa only [pow_succ, zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hc hc1).mul_const c)
  apply blockOperator_dist_le _ _ _ _ _ _ _ (pow_nonneg hc _) _ hP
  intro i
  rw [← projection_error_power _ _ (hPP i) (hMP i) (hPM i)]
  exact (norm_pow_le' _ (Nat.succ_pos n)).trans (by gcongr; exact hgap i)

end CoarseAssembly

end

end OAI
