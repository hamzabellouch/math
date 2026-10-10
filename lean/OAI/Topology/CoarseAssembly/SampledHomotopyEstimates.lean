import OAI.Topology.CoarseAssembly.SampledHomotopy
import OAI.Topology.CoarseAssembly.HomogeneousReindex

namespace OAI

/-! # Uniform norm estimates for arbitrarily many finite samples -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

theorem sampledFiniteSum_operator_sub_norm_le (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ σ : ℕ → Interval) (C : ℝ) (hC : 1 ≤ C)
    (hF : ∀ t, ‖h.operator t‖ ≤ C) (δ : ℝ) (hδ : 0 ≤ δ)
    (hnear : ∀ j, j < N → ‖h.operator (τ j) - h.operator (σ j)‖ ≤ δ) :
    ‖(show End (repeatedHilbert h.space) from (sampledFiniteSum h χ N τ C hC hF).operator) -
      (show End (repeatedHilbert h.space) from (sampledFiniteSum h χ N σ C hC hF).operator)‖ ≤ δ := by
  apply blockOperator_dist_le (hε := hδ)
  intro j
  change ‖(if j < N then h.operator (τ j) else 1) -
    (if j < N then h.operator (σ j) else 1)‖ ≤ δ
  by_cases hj : j < N
  · simpa only [ite_eq_left hj] using hnear j hj
  · simpa only [ite_eq_right hj, sub_self, norm_zero] using hδ

theorem sampledFiniteSum_representation_sub_norm_le (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ σ : ℕ → Interval) (C : ℝ) (hC : 1 ≤ C)
    (hF : ∀ t, ‖h.operator t‖ ≤ C) (a : A) (δ : ℝ) (hδ : 0 ≤ δ)
    (hnear : ∀ j, j < N → ‖h.representation (τ j) a - h.representation (σ j) a‖ ≤ δ) :
    ‖(show End (repeatedHilbert h.space) from (sampledFiniteSum h χ N τ C hC hF).representation a) -
      (show End (repeatedHilbert h.space) from (sampledFiniteSum h χ N σ C hC hF).representation a)‖ ≤ δ := by
  apply blockOperator_dist_le (hε := hδ)
  intro j
  change ‖(if j < N then h.representation (τ j) else
      characterProjectionRepresentation χ (1 : End h.space) (IsStarProjection.one _)) a -
    (if j < N then h.representation (σ j) else
      characterProjectionRepresentation χ (1 : End h.space) (IsStarProjection.one _)) a‖ ≤ δ
  by_cases hj : j < N
  · simpa only [ite_eq_left hj] using hnear j hj
  · simpa only [ite_eq_right hj, sub_self, norm_zero] using hδ

end CoarseAssembly.Analytic

end

end OAI
