import OAI.Topology.CoarseAssembly.FredholmModule
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace OAI

/-! # Finite subdivisions of an actual norm-continuous homotopy -/

noncomputable section

namespace CoarseAssembly.Analytic

def intervalGrid (N : ℕ) (hN : 0 < N) (j : ℕ) : Interval :=
  ⟨((min j N : ℕ) : ℝ) / N, div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    (div_le_one (Nat.cast_pos.mpr hN)).mpr (by exact_mod_cast Nat.min_le_right j N)⟩

@[simp] theorem intervalGrid_start (N : ℕ) (hN : 0 < N) : intervalGrid N hN 0 = start := by
  apply Subtype.ext
  simp [intervalGrid, start]

@[simp] theorem intervalGrid_finish (N : ℕ) (hN : 0 < N) : intervalGrid N hN N = finish := by
  apply Subtype.ext
  simp [intervalGrid, finish, Nat.ne_of_gt hN]

theorem intervalGrid_dist (N : ℕ) (hN : 0 < N) (j : ℕ) (hj : j < N) :
    dist (intervalGrid N hN (j + 1)) (intervalGrid N hN j) = (N : ℝ)⁻¹ := by
  change |((min (j + 1) N : ℕ) : ℝ) / N - ((min j N : ℕ) : ℝ) / N| = _
  rw [Nat.min_eq_left (Nat.succ_le_of_lt hj), Nat.min_eq_left hj.le, Nat.cast_succ]
  have he : ((j : ℝ) + 1) / N - (j : ℝ) / N = 1 / N := by ring
  rw [he, abs_of_nonneg (by positivity), one_div]

theorem exists_interval_subdivision {E : Type*} [PseudoMetricSpace E]
    (f : Interval → E) (hf : Continuous f) (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ j, j < N →
      dist (f (intervalGrid N hN (j + 1))) (f (intervalGrid N hN j)) < ε := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hf) ε hε
  obtain ⟨N, hN, hn⟩ := Real.exists_nat_pos_inv_lt hδ
  refine ⟨N, hN, fun j hj => hclose ?_⟩
  rw [intervalGrid_dist N hN j hj]
  exact hn

end CoarseAssembly.Analytic

end

end OAI
