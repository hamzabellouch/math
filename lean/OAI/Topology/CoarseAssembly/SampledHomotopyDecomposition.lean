import OAI.Topology.CoarseAssembly.SampledHomotopy
import OAI.Topology.CoarseAssembly.FiniteCycleDecomposition
import OAI.Topology.CoarseAssembly.HomogeneousReindex

namespace OAI

/-! # Endpoint and interior decompositions of finite homotopy samples -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

def sampledFiniteSum_head_tail (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ : ℕ → Interval) (C : ℝ) (hC : 1 ≤ C)
    (hF : ∀ t, ‖h.operator t‖ ≤ C) :
    (h.eval (τ 0)).IsDirectSum
      (sampledFiniteSum h χ N (fun j => τ (j + 1)) C hC hF)
      (sampledFiniteSum h χ (N + 1) τ C hC hF) where
  left := summandIsometry (fun _ => h.space) 0
  right := tailInsert (fun _ => h.space)
  orthogonal := head_tail_orthogonal _
  exhaustive := head_tail_exhaustive _
  representation_eq a := by
    change blockOperator (fun j => (if j < N + 1 then h.representation (τ j) else
      characterProjectionRepresentation χ (1 : End h.space) (IsStarProjection.one _)) a)
      ‖a‖ (norm_nonneg _) _ = _
    erw [blockOperator_head_tail]
    simp only [Nat.add_lt_add_iff_right, Nat.zero_lt_succ, ite_true]
    rfl
  operator_eq := by
    change blockOperator (fun j => if j < N + 1 then h.operator (τ j) else 1)
      C (zero_le_one.trans hC) _ = _
    erw [blockOperator_head_tail]
    simp only [Nat.add_lt_add_iff_right, Nat.zero_lt_succ, ite_true]
    rfl

/-- Put the last endpoint first, leaving the interior list in its original order. -/
def lastEndpointFirst (N : ℕ) (τ : ℕ → Interval) (j : ℕ) : Interval :=
  if j = 0 then τ (N + 1) else τ j

@[simp] theorem lastEndpointFirst_zero (N : ℕ) (τ : ℕ → Interval) :
    lastEndpointFirst N τ 0 = τ (N + 1) := by simp [lastEndpointFirst]

@[simp] theorem lastEndpointFirst_succ (N : ℕ) (τ : ℕ → Interval) (j : ℕ) :
    lastEndpointFirst N τ (j + 1) = τ (j + 1) := by simp [lastEndpointFirst]

def sampledFiniteSum_rotate (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ : ℕ → Interval) (C : ℝ) (hC : 1 ≤ C)
    (hF : ∀ t, ‖h.operator t‖ ≤ C) :
    (sampledFiniteSum h χ (N + 1) (lastEndpointFirst N τ) C hC hF).UnitaryEquivalent
      (sampledFiniteSum h χ (N + 1) (fun j => τ (j + 1)) C hC hF) where
  unitary := repeatedReindexEquiv h.space (rotatePrefix N)
  representation_eq a := by
    symm
    change operatorConjugation (repeatedReindexEquiv h.space (rotatePrefix N)).toLinearIsometry
      (blockOperator (fun j => (if j < N + 1 then h.representation (lastEndpointFirst N τ j) else
        characterProjectionRepresentation χ (1 : End h.space) (IsStarProjection.one _)) a)
        ‖a‖ (norm_nonneg _) _) = _
    erw [blockOperator_reindex]
    ext x j
    change (sampledCycle h χ (N + 1) (lastEndpointFirst N τ) ((rotatePrefix N).symm j)).representation a (x j) =
      (sampledCycle h χ (N + 1) (fun j => τ (j + 1)) j).representation a (x j)
    by_cases hj : j < N
    · rw [rotatePrefix_inverse_lt N j hj]
      simp [sampledCycle, lastEndpointFirst, Nat.lt_add_one_of_lt hj, hj]
      rfl
    · by_cases he : j = N
      · subst j
        simp [sampledCycle, lastEndpointFirst]
        rfl
      · have hgt : N < j := by omega
        rw [rotatePrefix_inverse_gt N j hgt]
        simp [sampledCycle, show ¬j < N + 1 by omega]
        rfl
  operator_eq := by
    symm
    change operatorConjugation (repeatedReindexEquiv h.space (rotatePrefix N)).toLinearIsometry
      (blockOperator (fun j => if j < N + 1 then h.operator (lastEndpointFirst N τ j) else 1)
        C (zero_le_one.trans hC) _) = _
    erw [blockOperator_reindex]
    ext x j
    change (sampledCycle h χ (N + 1) (lastEndpointFirst N τ) ((rotatePrefix N).symm j)).operator (x j) =
      (sampledCycle h χ (N + 1) (fun j => τ (j + 1)) j).operator (x j)
    by_cases hj : j < N
    · rw [rotatePrefix_inverse_lt N j hj]
      simp [sampledCycle, lastEndpointFirst, Nat.lt_add_one_of_lt hj, hj]
      rfl
    · by_cases he : j = N
      · subst j
        simp [sampledCycle, lastEndpointFirst]
        rfl
      · have hgt : N < j := by omega
        rw [rotatePrefix_inverse_gt N j hgt]
        simp [sampledCycle, show ¬j < N + 1 by omega]
        rfl

end CoarseAssembly.Analytic

end

end OAI
