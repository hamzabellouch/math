import OAI.Topology.CoarseAssembly.FamilyCoefficientEmbedding

namespace OAI

/-! # Ample coefficient choices do not affect a whole-family Roe boundary -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)]
  {E : ℕ → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Boundary of a family after specified coefficient embeddings. -/
def coefficientFamilyBoundary (o : ∀ i, Q i) (A : ∀ i, Operator (Q i) (E i))
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
    (r : ℝ) (hr : 0 ≤ r) (hp : ∀ i, PropagationLE r (A i))
    (hs : ∀ i, IsSelfAdjoint (A i))
    (hsq : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (Q i) (E i))))
    (V : ∀ i, E i →ₗᵢ[ℂ] H) :
    letI := separatedMetric o
    OperatorKTheory.K1 (algebra (X := Sigma Q) (H := H)) := by
  let := separatedMetric o
  exact separatedFamilyBoundary (H := H) o (fun i => coefficientExtension (V i) (A i))
    (C + 2) (by linarith)
    (fun i => (coefficientExtension_norm_le (V i) (A i)).trans (by linarith [hA i]))
    r hr (fun i => coefficientExtension_propagation (V i) hr (hp i))
    (fun i => coefficientExtension_selfAdjoint (V i) (A i) (hs i))
    (fun i => coefficientExtension_square_compact (V i) (A i) (hsq i))

/-- This compares whole-union classes directly, without passing to component K₁ classes. -/
theorem coefficientFamilyBoundary_independent (o : ∀ i, Q i)
    (A : ∀ i, Operator (Q i) (E i)) (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
    (r : ℝ) (hr : 0 ≤ r) (hp : ∀ i, PropagationLE r (A i))
    (hs : ∀ i, IsSelfAdjoint (A i))
    (hsq : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (Q i) (E i))))
    (V W : ∀ i, E i →ₗᵢ[ℂ] H) :
    letI := separatedMetric o
    coefficientFamilyBoundary o A C hC hA r hr hp hs hsq V =
      coefficientFamilyBoundary o A C hC hA r hr hp hs hsq W := by
  let := separatedMetric o
  let AV := fun i => coefficientExtension (V i) (A i)
  let AW := fun i => coefficientExtension (W i) (A i)
  have hC' : 0 ≤ C + 2 := by linarith
  have hAV : ∀ i, ‖AV i‖ ≤ C + 2 := fun i =>
    (coefficientExtension_norm_le (V i) (A i)).trans (by linarith [hA i])
  have hAW : ∀ i, ‖AW i‖ ≤ C + 2 := fun i =>
    (coefficientExtension_norm_le (W i) (A i)).trans (by linarith [hA i])
  have hpV : ∀ i, PropagationLE r (AV i) := fun i =>
    coefficientExtension_propagation (V i) hr (hp i)
  have hpW : ∀ i, PropagationLE r (AW i) := fun i =>
    coefficientExtension_propagation (W i) hr (hp i)
  have hsV : ∀ i, IsSelfAdjoint (AV i) := fun i =>
    coefficientExtension_selfAdjoint (V i) (A i) (hs i)
  have hsW : ∀ i, IsSelfAdjoint (AW i) := fun i =>
    coefficientExtension_selfAdjoint (W i) (A i) (hs i)
  have hsqV : ∀ i, IsCompactOperator (AV i * AV i - (1 : Operator (Q i) H)) := fun i =>
    coefficientExtension_square_compact (V i) (A i) (hsq i)
  have hsqW : ∀ i, IsCompactOperator (AW i * AW i - (1 : Operator (Q i) H)) := fun i =>
    coefficientExtension_square_compact (W i) (A i) (hsq i)
  let F := separatedFamilyMultiplier (H := H) o AV (C + 2) hC' hAV r hr hpV
  let G := separatedFamilyMultiplier (H := H) o AW (C + 2) hC' hAW r hr hpW
  have hFs := separatedFamilyMultiplier_selfAdjoint o AV (C + 2) hC' hAV r hr hpV hsV
  have hGs := separatedFamilyMultiplier_selfAdjoint o AW (C + 2) hC' hAW r hr hpW hsW
  have hFd := diagonalFamily_square_mem_roe o AV (C + 2) hC' hAV r hr hpV hsV hsqV
  have hGd := diagonalFamily_square_mem_roe o AW (C + 2) hC' hAW r hr hpW hsW hsqW
  change multiplierBoundaryClass F hFs hFd = multiplierBoundaryClass G hGs hGd
  exact multiplierBoundaryClass_embedding (familyCoefficientIsometry V) (familyCoefficientIsometry W)
    (blockOperator A C hC hA) (blockOperator_selfAdjoint A C hC hA hs) F G
    (separatedFamilyMultiplier_selfAdjoint o AV (C + 2) hC' hAV r hr hpV hsV)
    (separatedFamilyMultiplier_selfAdjoint o AW (C + 2) hC' hAW r hr hpW hsW)
    (diagonalFamily_square_mem_roe o AV (C + 2) hC' hAV r hr hpV hsV hsqV)
    (diagonalFamily_square_mem_roe o AW (C + 2) hC' hAW r hr hpW hsW hsqW)
    (familyCoefficient_extension V A C hC hA (C + 2) hC' hAV).symm
    (familyCoefficient_extension W A C hC hA (C + 2) hC' hAW).symm
    (finitePropagation_multiplier (separatedMetric_closedBall_finite o) le_rfl
      (familyEmbeddingTransition_propagation V W))

end CoarseAssembly.DiscreteRoe

end

end OAI
