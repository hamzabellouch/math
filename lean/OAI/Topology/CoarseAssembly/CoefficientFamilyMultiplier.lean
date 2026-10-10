import OAI.Topology.CoarseAssembly.FamilyEmbeddingIndependence

namespace OAI

/-! # The actual multiplier underlying a coefficient-family boundary -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)]
  {E : ℕ → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (o : ∀ i, Q i) (A : ∀ i, Operator (Q i) (E i))
  (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
  (r : ℝ) (hr : 0 ≤ r) (hp : ∀ i, PropagationLE r (A i))
  (V : ∀ i, E i →ₗᵢ[ℂ] H)

def coefficientFamilyMultiplier :
    letI := separatedMetric o
    multiplierAlgebra (X := Sigma Q) (H := H) := by
  let := separatedMetric o
  exact separatedFamilyMultiplier o (fun i => coefficientExtension (V i) (A i))
    (C + 2) (by linarith)
    (fun i => (coefficientExtension_norm_le (V i) (A i)).trans (by linarith [hA i]))
    r hr (fun i => coefficientExtension_propagation (V i) hr (hp i))

theorem coefficientFamilyMultiplier_value :
    letI := separatedMetric o
    (coefficientFamilyMultiplier o A C hC hA r hr hp V).val =
      isometricExtension (familyCoefficientIsometry V) (blockOperator A C hC hA) := by
  let := separatedMetric o
  exact (familyCoefficient_extension V A C hC hA (C + 2) (by linarith)
    (fun i => (coefficientExtension_norm_le (V i) (A i)).trans (by linarith [hA i]))).symm

theorem coefficientFamilyMultiplier_selfAdjoint (hs : ∀ i, IsSelfAdjoint (A i)) :
    letI := separatedMetric o
    IsSelfAdjoint (coefficientFamilyMultiplier o A C hC hA r hr hp V) := by
  let := separatedMetric o
  exact separatedFamilyMultiplier_selfAdjoint o (fun i => coefficientExtension (V i) (A i))
    (C + 2) (by linarith)
    (fun i => (coefficientExtension_norm_le (V i) (A i)).trans (by linarith [hA i]))
    r hr (fun i => coefficientExtension_propagation (V i) hr (hp i))
    (fun i => coefficientExtension_selfAdjoint (V i) (A i) (hs i))

theorem coefficientFamilyMultiplier_defect (hs : ∀ i, IsSelfAdjoint (A i))
    (hsq : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (Q i) (E i)))) :
    letI := separatedMetric o
    (coefficientFamilyMultiplier o A C hC hA r hr hp V).val ^ 2 - 1 ∈
      algebra (X := Sigma Q) (H := H) := by
  let := separatedMetric o
  exact diagonalFamily_square_mem_roe o (fun i => coefficientExtension (V i) (A i))
    (C + 2) (by linarith)
    (fun i => (coefficientExtension_norm_le (V i) (A i)).trans (by linarith [hA i]))
    r hr (fun i => coefficientExtension_propagation (V i) hr (hp i))
    (fun i => coefficientExtension_selfAdjoint (V i) (A i) (hs i))
    (fun i => coefficientExtension_square_compact (V i) (A i) (hsq i))

theorem coefficientFamilyBoundary_eq_multiplier (hs : ∀ i, IsSelfAdjoint (A i))
    (hsq : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (Q i) (E i)))) :
    letI := separatedMetric o
    coefficientFamilyBoundary o A C hC hA r hr hp hs hsq V =
      multiplierBoundaryClass (coefficientFamilyMultiplier o A C hC hA r hr hp V)
        (coefficientFamilyMultiplier_selfAdjoint o A C hC hA r hr hp V hs)
        (coefficientFamilyMultiplier_defect o A C hC hA r hr hp V hs hsq) := rfl

end CoarseAssembly.DiscreteRoe

end

end OAI
