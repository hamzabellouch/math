import OAI.Topology.CoarseAssembly.ProjectionBlocks
import OAI.Topology.CoarseAssembly.CoefficientDecomposition

namespace OAI

/-! # Reducing decompositions and intertwiners on bounded Hilbert sums -/

noncomputable section

namespace CoarseAssembly

variable {I : Type*} {E F G : I → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)] [∀ i, CompleteSpace (F i)]
  [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℂ (G i)] [∀ i, CompleteSpace (G i)]

theorem blockIsometry_adjoint_coordinate (V : ∀ i, E i →ₗᵢ[ℂ] G i) (v : lp G 2) (i : I) :
    (blockIsometry V).toContinuousLinearMap.adjoint v i =
      (V i).toContinuousLinearMap.adjoint (v i) := by
  rw [blockIsometry_toCLM, blockOperator_adjoint]
  rfl

omit [∀ i, CompleteSpace (F i)] in
theorem blockIsometry_orthogonal (V : ∀ i, E i →ₗᵢ[ℂ] G i) (W : ∀ i, F i →ₗᵢ[ℂ] G i)
    (hVW : ∀ i, (V i).toContinuousLinearMap.adjoint.comp (W i).toContinuousLinearMap = 0) :
    (blockIsometry V).toContinuousLinearMap.adjoint.comp (blockIsometry W).toContinuousLinearMap = 0 := by
  ext v i
  change (blockIsometry V).toContinuousLinearMap.adjoint (blockIsometry W v) i = 0
  rw [blockIsometry_adjoint_coordinate, blockIsometry_apply]
  exact DFunLike.congr_fun (hVW i) (v i)

theorem blockIsometry_exhaustive (V : ∀ i, E i →ₗᵢ[ℂ] G i) (W : ∀ i, F i →ₗᵢ[ℂ] G i)
    (hex : ∀ i, (V i).toContinuousLinearMap.comp (V i).toContinuousLinearMap.adjoint +
      (W i).toContinuousLinearMap.comp (W i).toContinuousLinearMap.adjoint = 1) :
    (blockIsometry V).toContinuousLinearMap.comp (blockIsometry V).toContinuousLinearMap.adjoint +
      (blockIsometry W).toContinuousLinearMap.comp (blockIsometry W).toContinuousLinearMap.adjoint = 1 := by
  ext v i
  change blockIsometry V ((blockIsometry V).toContinuousLinearMap.adjoint v) i +
    blockIsometry W ((blockIsometry W).toContinuousLinearMap.adjoint v) i = v i
  rw [blockIsometry_apply, blockIsometry_apply,
    blockIsometry_adjoint_coordinate, blockIsometry_adjoint_coordinate]
  exact DFunLike.congr_fun (hex i) (v i)

omit [∀ i, CompleteSpace (E i)] [∀ i, CompleteSpace (G i)] in
theorem blockOperator_intertwines (V : ∀ i, E i →ₗᵢ[ℂ] G i)
    (A : ∀ i, E i →L[ℂ] E i) (B : ∀ i, G i →L[ℂ] G i)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D)
    (hV : ∀ i, (B i).comp (V i).toContinuousLinearMap = (V i).toContinuousLinearMap.comp (A i)) :
    (blockOperator B D hD hB).comp (blockIsometry V).toContinuousLinearMap =
      (blockIsometry V).toContinuousLinearMap.comp (blockOperator A C hC hA) := by
  ext v i
  exact DFunLike.congr_fun (hV i) (v i)

theorem blockOperator_decomposition
    (V : ∀ i, E i →ₗᵢ[ℂ] G i) (W : ∀ i, F i →ₗᵢ[ℂ] G i)
    (hex : ∀ i, (V i).toContinuousLinearMap.comp (V i).toContinuousLinearMap.adjoint +
      (W i).toContinuousLinearMap.comp (W i).toContinuousLinearMap.adjoint = 1)
    (A : ∀ i, E i →L[ℂ] E i) (B : ∀ i, F i →L[ℂ] F i) (T : ∀ i, G i →L[ℂ] G i)
    (C D K : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D) (hT : ∀ i, ‖T i‖ ≤ K)
    (hV : ∀ i, (T i).comp (V i).toContinuousLinearMap = (V i).toContinuousLinearMap.comp (A i))
    (hW : ∀ i, (T i).comp (W i).toContinuousLinearMap = (W i).toContinuousLinearMap.comp (B i)) :
    blockOperator T K hK hT =
      operatorConjugation (blockIsometry V) (blockOperator A C hC hA) +
        operatorConjugation (blockIsometry W) (blockOperator B D hD hB) :=
  orthogonal_isometries_decompose _ _ (blockIsometry_exhaustive V W hex) _ _ _
    (blockOperator_intertwines V A T C K hC hK hA hT hV)
    (blockOperator_intertwines W B T D K hD hK hB hT hW)

end CoarseAssembly

end

end OAI
