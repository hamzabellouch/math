import OAI.Topology.CoarseAssembly.FiniteCycleSum
import OAI.Topology.CoarseAssembly.CharacterExtension

namespace OAI

/-! # Actual finite samples of an analytic homotopy

The inactive summands are degenerate character cycles on the same Hilbert
space. Thus the ambient countable Hilbert sum does not depend on the samples.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

def sampledCycle (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ : ℕ → Interval) (j : ℕ) : OddCycle A where
  space := h.space
  representation := if j < N then h.representation (τ j) else
    characterProjectionRepresentation χ (1 : End h.space) (IsStarProjection.one _)
  operator := if j < N then h.operator (τ j) else 1
  commutator_compact a := by
    by_cases hj : j < N
    · simpa only [ite_eq_left hj] using h.commutator_compact (τ j) a
    · simp only [ite_eq_right hj, one_mul, mul_one, sub_self]
      exact isCompactOperator_zero
  square_compact a := by
    by_cases hj : j < N
    · simpa only [ite_eq_left hj] using h.square_compact (τ j) a
    · simp only [ite_eq_right hj, one_mul, sub_self, zero_mul]
      exact isCompactOperator_zero
  adjoint_compact a := by
    by_cases hj : j < N
    · simpa only [ite_eq_left hj] using h.adjoint_compact (τ j) a
    · simp only [ite_eq_right hj, star_one, sub_self, zero_mul]
      exact isCompactOperator_zero

theorem sampledCycle_active (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ : ℕ → Interval) (j : ℕ) (hj : j < N) :
    sampledCycle h χ N τ j = h.eval (τ j) := by
  simp only [sampledCycle, ite_eq_left hj, OddHomotopy.eval]

theorem sampledCycle_inactive_degenerate (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ : ℕ → Interval) (j : ℕ) (hj : N ≤ j) :
    (sampledCycle h χ N τ j).Degenerate := by
  have he : sampledCycle h χ N τ j = identityOperatorCycle
      (characterProjectionRepresentation χ (1 : End h.space) (IsStarProjection.one _)) := by
    simp only [sampledCycle, identityOperatorCycle, ite_eq_right (not_lt.mpr hj)]
  rw [he]
  exact identityOperatorCycle_degenerate _

theorem sampledCycle_unital (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ : ℕ → Interval) (j : ℕ)
    (hπ : ∀ t, h.representation t 1 = 1) :
    (sampledCycle h χ N τ j).representation 1 = 1 := by
  change (if j < N then h.representation (τ j) else
    characterProjectionRepresentation χ (1 : End h.space) (IsStarProjection.one _)) 1 = 1
  split_ifs with hj
  · exact hπ (τ j)
  · simp [characterProjectionRepresentation]

theorem sampledCycle_selfAdjoint (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ : ℕ → Interval) (j : ℕ)
    (hs : ∀ t, IsSelfAdjoint (h.operator t)) :
    IsSelfAdjoint (sampledCycle h χ N τ j).operator := by
  change IsSelfAdjoint (if j < N then h.operator (τ j) else 1)
  split_ifs
  · exact hs (τ j)
  · exact IsSelfAdjoint.one _

theorem sampledCycle_norm_le (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ : ℕ → Interval) (j : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (hF : ∀ t, ‖h.operator t‖ ≤ C) : ‖(sampledCycle h χ N τ j).operator‖ ≤ C := by
  change ‖if j < N then h.operator (τ j) else 1‖ ≤ C
  split_ifs
  · exact hF (τ j)
  · exact ContinuousLinearMap.norm_id_le.trans hC

def sampledFiniteSum (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ : ℕ → Interval) (C : ℝ) (hC : 1 ≤ C)
    (hF : ∀ t, ‖h.operator t‖ ≤ C) : OddCycle A :=
  finiteActiveCycle (sampledCycle h χ N τ) C (zero_le_one.trans hC)
    (fun j => sampledCycle_norm_le h χ N τ j C hC hF) N
    (fun j => sampledCycle_inactive_degenerate h χ N τ j)

theorem sampledFiniteSum_unital (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ : ℕ → Interval) (C : ℝ) (hC : 1 ≤ C)
    (hF : ∀ t, ‖h.operator t‖ ≤ C) (hπ : ∀ t, h.representation t 1 = 1) :
    (sampledFiniteSum h χ N τ C hC hF).representation 1 = 1 :=
  finiteActiveCycle_unital _ _ _ _ _ _ (fun j => sampledCycle_unital h χ N τ j hπ)

theorem sampledFiniteSum_selfAdjoint (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ : ℕ → Interval) (C : ℝ) (hC : 1 ≤ C)
    (hF : ∀ t, ‖h.operator t‖ ≤ C) (hs : ∀ t, IsSelfAdjoint (h.operator t)) :
    IsSelfAdjoint (sampledFiniteSum h χ N τ C hC hF).operator :=
  finiteActiveCycle_selfAdjoint _ _ _ _ _ _ (fun j => sampledCycle_selfAdjoint h χ N τ j hs)

theorem sampledFiniteSum_norm_le (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ : ℕ → Interval) (C : ℝ) (hC : 1 ≤ C)
    (hF : ∀ t, ‖h.operator t‖ ≤ C) : ‖(sampledFiniteSum h χ N τ C hC hF).operator‖ ≤ C :=
  finiteActiveCycle_norm _ _ _ _ _ _

end CoarseAssembly.Analytic

end

end OAI
