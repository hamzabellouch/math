import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.ProjectionBlocks
import OAI.Topology.CoarseAssembly.RoeRows
import OAI.Topology.CoarseAssembly.SeparatedUnion

namespace OAI

/-! # Uniform diagonal families on the actual separated vertex union -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {V : ℕ → Type*} [∀ i, DecidableEq (V i)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [∀ i, DecidableEq (V i)] [CompleteSpace H] in
@[simp] theorem diagonalFamily_apply (A : ∀ i, Operator (V i) H) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i, ‖A i‖ ≤ C) (v : Module (Sigma V) H) (i : ℕ) (x : V i) :
    diagonalFamily A C hC hA v ⟨i, x⟩ = A i (rowVector v i) x := rfl

omit [∀ i, DecidableEq (V i)] [CompleteSpace H] in
theorem diagonalFamily_norm_le (A : ∀ i, Operator (V i) H) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i, ‖A i‖ ≤ C) : ‖diagonalFamily A C hC hA‖ ≤ C :=
  (flattenOperator_norm_le _).trans (blockOperator_norm_le _ _ _ _)

omit [∀ i, DecidableEq (V i)] [CompleteSpace H] in
theorem rowVector_diagonalFamily (A : ∀ i, Operator (V i) H) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i, ‖A i‖ ≤ C) (v : Module (Sigma V) H) (i : ℕ) :
    rowVector (diagonalFamily A C hC hA v) i = A i (rowVector v i) := by
  apply lp.ext
  rfl

omit [CompleteSpace H] in
@[simp] theorem entry_diagonalFamily_same (A : ∀ i, Operator (V i) H)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) (i : ℕ) (x y : V i) :
    entry (diagonalFamily A C hC hA) ⟨i, x⟩ ⟨i, y⟩ = entry (A i) x y := by
  ext v
  simp only [entry_apply, diagonalFamily_apply, rowVector_single_same]

omit [CompleteSpace H] in
theorem entry_diagonalFamily_ne (A : ∀ i, Operator (V i) H)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) {i j : ℕ} (hij : i ≠ j)
    (x : V i) (y : V j) :
    entry (diagonalFamily A C hC hA) ⟨i, x⟩ ⟨j, y⟩ = 0 := by
  ext v
  simp only [entry_apply, diagonalFamily_apply, rowVector_single_ne hij, map_zero,
    lp.coeFn_zero, Pi.zero_apply, zero_apply]

omit [∀ i, DecidableEq (V i)] in
theorem diagonalFamily_selfAdjoint (A : ∀ i, Operator (V i) H)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) (hself : ∀ i, IsSelfAdjoint (A i)) :
    IsSelfAdjoint (diagonalFamily A C hC hA) := by
  have hb : IsSelfAdjoint (blockOperator A C hC hA) := by
    change (blockOperator A C hC hA).adjoint = _
    rw [blockOperator_adjoint]
    apply ContinuousLinearMap.ext
    intro v
    apply lp.ext
    funext i
    change (A i).adjoint (v i) = A i (v i)
    have hi : (A i).adjoint = A i := (hself i).star_eq
    exact DFunLike.congr_fun hi (v i)
  rw [diagonalFamily, flattenOperator_eq_conjugation]
  exact hb.map (operatorConjugationHom (flattenEquiv (Q := V) (H := H)).toLinearIsometry)

variable [∀ i, MetricSpace (V i)] (o : ∀ i, V i)


omit [CompleteSpace H] in
theorem diagonalFamily_propagation (A : ∀ i, Operator (V i) H)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) (r : ℝ)
    (hp : ∀ i, PropagationLE r (A i)) :
    letI := separatedMetric o
    PropagationLE r (diagonalFamily A C hC hA) := by
  let := separatedMetric o
  rintro ⟨i, x⟩ ⟨j, y⟩ hxy
  by_cases hij : i = j
  · subst j
    rw [entry_diagonalFamily_same]
    apply hp i x y
    simpa only [show dist (⟨i, x⟩ : Sigma V) ⟨i, y⟩ = dist x y from
      separatedDist_same o i x y] using hxy
  · exact entry_diagonalFamily_ne A C hC hA hij x y

end CoarseAssembly.DiscreteRoe

end

end OAI
