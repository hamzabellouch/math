import OAI.Topology.CoarseAssembly.EmbeddingBoundaryComparison
import OAI.Topology.CoarseAssembly.ProjectionBlocks

namespace OAI

/-! # Pointwise coefficient transitions have propagation zero -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X : Type*} [DecidableEq X] [PseudoMetricSpace X]
  {E : X → Type*} [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℂ (E x)] [∀ x, CompleteSpace (E x)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [DecidableEq X] [PseudoMetricSpace X] in
theorem blockIsometry_adjoint_apply (V : ∀ x, E x →ₗᵢ[ℂ] H)
    (v : Module X H) (x : X) :
    (blockIsometry V).toContinuousLinearMap.adjoint v x =
      (V x).toContinuousLinearMap.adjoint (v x) := by
  rw [blockIsometry_toCLM, blockOperator_adjoint]
  rfl

omit [DecidableEq X] [PseudoMetricSpace X] in
theorem pointwiseEmbeddingTransition_apply (V W : ∀ x, E x →ₗᵢ[ℂ] H)
    (v : Module X H) (x : X) :
    embeddingTransition (blockIsometry V) (blockIsometry W) v x =
      W x ((V x).toContinuousLinearMap.adjoint (v x)) := by
  change (blockIsometry W) ((blockIsometry V).toContinuousLinearMap.adjoint v) x = _
  rw [blockIsometry_apply, blockIsometry_adjoint_apply]

theorem pointwiseEmbeddingTransition_propagation (V W : ∀ x, E x →ₗᵢ[ℂ] H) :
    PropagationLE 0 (embeddingTransition (blockIsometry V) (blockIsometry W)) := by
  intro x y hxy
  have hne : x ≠ y := by rintro rfl; simp at hxy
  ext h
  simp [entry_apply, pointwiseEmbeddingTransition_apply, lp.single_apply,
    hne]

theorem pointwiseEmbeddingTransition_multiplier
    (finiteBalls : ∀ x : X, ∀ r : ℝ, (Metric.closedBall x r).Finite)
    (V W : ∀ x, E x →ₗᵢ[ℂ] H) :
    RoeMultiplier (embeddingTransition (blockIsometry V) (blockIsometry W)) :=
  finitePropagation_multiplier finiteBalls le_rfl (pointwiseEmbeddingTransition_propagation V W)

/-- Choice of pointwise embeddings does not change the actual Roe boundary class. -/
theorem multiplierBoundaryClass_pointwiseEmbedding
    (finiteBalls : ∀ x : X, ∀ r : ℝ, (Metric.closedBall x r).Finite)
    (V W : ∀ x, E x →ₗᵢ[ℂ] H) (S : lp E 2 →L[ℂ] lp E 2) (hS : IsSelfAdjoint S)
    (F G : multiplierAlgebra (X := X) (H := H)) (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G)
    (hFd : F.val ^ 2 - 1 ∈ algebra (X := X) (H := H))
    (hGd : G.val ^ 2 - 1 ∈ algebra (X := X) (H := H))
    (hFV : F.val = isometricExtension (blockIsometry V) S)
    (hGW : G.val = isometricExtension (blockIsometry W) S) :
    multiplierBoundaryClass F hF hFd = multiplierBoundaryClass G hG hGd :=
  multiplierBoundaryClass_embedding (blockIsometry V) (blockIsometry W) S hS
    F G hF hG hFd hGd hFV hGW (pointwiseEmbeddingTransition_multiplier finiteBalls V W)

end CoarseAssembly.DiscreteRoe

end

end OAI
