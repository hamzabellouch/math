import OAI.Topology.CoarseAssembly.RoeCompactRows
import Mathlib.Topology.Compactness.Compact

namespace OAI

/-! # Finite-support approximation of multiplication operators -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open Filter
open scoped ZeroAtInfty Topology

variable {X H : Type*} [DecidableEq X] [TopologicalSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem diagonalApproximation_norm (f : C₀(X, ℂ)) (s : Finset X)
    (ε : ℝ) (hε : 0 ≤ ε) (hs : ∀ x, x ∉ s → ‖f x‖ ≤ ε) :
    ‖diagonalMultiplier (H := H) f - finiteDiagonal (H := H) f s‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro v
  calc
    _ ≤ ‖ε • lp.toNorm v‖ := by
      apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
      intro x
      change ‖diagonalMultiplier f v x - finiteDiagonal f s v x‖ ≤ ‖ε * ‖v x‖‖
      rw [diagonalMultiplier_apply, finiteDiagonal_apply,
        Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hε (norm_nonneg _))]
      by_cases hx : x ∈ s
      · rw [ite_eq_left hx, sub_self, norm_zero]
        positivity
      · rw [ite_eq_right hx, sub_zero, norm_smul]
        exact mul_le_mul_of_nonneg_right (hs x hx) (norm_nonneg _)
    _ = ε * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε, lp.norm_toNorm]

variable [DiscreteTopology X]

theorem finiteDiagonal_tendsto (f : C₀(X, ℂ)) :
    Tendsto (fun s : Finset X => finiteDiagonal (H := H) f s) atTop
      (𝓝 (diagonalMultiplier (H := H) f)) := by
  apply (tendsto_iff_norm_sub_tendsto_zero (E := Operator X H)
    (f := fun s : Finset X => finiteDiagonal (H := H) f s)
    (b := diagonalMultiplier (H := H) f)).mpr
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall : {x : X | dist (f x) 0 < ε / 2} ∈ cocompact X :=
    Metric.tendsto_nhds.mp (zero_at_infty f) (ε / 2) (by positivity)
  obtain ⟨K, hK, hbound⟩ := mem_cocompact.mp hsmall
  filter_upwards [eventually_ge_atTop hK.finite_of_discrete.toFinset] with s hs
  simp only [dist_zero_right, norm_norm]
  rw [norm_sub_rev (finiteDiagonal (H := H) f s) (diagonalMultiplier (H := H) f)]
  apply (diagonalApproximation_norm f s (ε / 2) (by positivity) ?_).trans_lt (by linarith)
  intro x hx
  have hxK : x ∉ K := by
    intro h
    exact hx (hs (hK.finite_of_discrete.mem_toFinset.mpr h))
  have hb := hbound hxK
  change dist (f x) 0 < ε / 2 at hb
  exact (by simpa only [dist_zero_right] using hb.le)

end CoarseAssembly.DiscreteRoe

end

end OAI
