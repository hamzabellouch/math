import OAI.Topology.CoarseAssembly.CoefficientFamilyMultiplier
import OAI.Topology.CoarseAssembly.BlockIsometryRelations
import OAI.Topology.CoarseAssembly.IsometricDecomposition
import OAI.Topology.CoarseAssembly.MultiplierOrthogonalEmbeddings

namespace OAI

/-! # Orthogonal decomposition of a whole coefficient family -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)]
  {E F G : ℕ → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)] [∀ i, CompleteSpace (F i)]
  [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℂ (G i)] [∀ i, CompleteSpace (G i)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)]
  [∀ i, CompleteSpace (E i)] [∀ i, CompleteSpace (G i)] [CompleteSpace H] in
theorem familyCoefficientIsometry_comp (U : ∀ i, G i →ₗᵢ[ℂ] H) (V : ∀ i, E i →ₗᵢ[ℂ] G i) :
    (familyCoefficientIsometry (Q := Q) U).comp
      (blockIsometry (fun i => coefficientIsometry (X := Q i) (V i))) =
        familyCoefficientIsometry (fun i => (U i).comp (V i)) := by
  ext v p
  rcases p with ⟨i, x⟩
  rfl

omit [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)]
  [∀ i, CompleteSpace (F i)] in
theorem familyCoefficientIsometry_orthogonal
    (U : ∀ i, G i →ₗᵢ[ℂ] H) (L : ∀ i, E i →ₗᵢ[ℂ] G i) (R : ∀ i, F i →ₗᵢ[ℂ] G i)
    (hLR : ∀ i, (L i).toContinuousLinearMap.adjoint.comp (R i).toContinuousLinearMap = 0) :
    (familyCoefficientIsometry (Q := Q) (fun i => (U i).comp (L i))).toContinuousLinearMap.adjoint.comp
      (familyCoefficientIsometry (fun i => (U i).comp (R i))).toContinuousLinearMap = 0 := by
  have h := isometry_comp_orthogonal (familyCoefficientIsometry (Q := Q) U)
    (blockIsometry (fun i => coefficientIsometry (X := Q i) (L i)))
    (blockIsometry (fun i => coefficientIsometry (X := Q i) (R i)))
    (blockIsometry_orthogonal _ _ (fun i => coefficientIsometry_orthogonal (L i) (R i) (hLR i)))
  simpa only [familyCoefficientIsometry_comp] using h

theorem coefficientFamilyMultiplier_decomposition_value
    (o : ∀ i, Q i) (A : ∀ i, Operator (Q i) (E i)) (B : ∀ i, Operator (Q i) (F i))
    (T : ∀ i, Operator (Q i) (G i))
    (C D K : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D) (hT : ∀ i, ‖T i‖ ≤ K)
    (r : ℝ) (hr : 0 ≤ r) (hpT : ∀ i, PropagationLE r (T i))
    (L : ∀ i, E i →ₗᵢ[ℂ] G i) (R : ∀ i, F i →ₗᵢ[ℂ] G i)
    (hex : ∀ i, (L i).toContinuousLinearMap.comp (L i).toContinuousLinearMap.adjoint +
      (R i).toContinuousLinearMap.comp (R i).toContinuousLinearMap.adjoint = 1)
    (hL : ∀ i, (T i).comp (coefficientIsometry (L i)).toContinuousLinearMap =
      (coefficientIsometry (L i)).toContinuousLinearMap.comp (A i))
    (hR : ∀ i, (T i).comp (coefficientIsometry (R i)).toContinuousLinearMap =
      (coefficientIsometry (R i)).toContinuousLinearMap.comp (B i))
    (U : ∀ i, G i →ₗᵢ[ℂ] H) :
    letI := separatedMetric o
    (coefficientFamilyMultiplier o T K hK hT r hr hpT U).val =
      1 + operatorConjugation (familyCoefficientIsometry (fun i => (U i).comp (L i)))
        (blockOperator A C hC hA - 1) +
      operatorConjugation (familyCoefficientIsometry (fun i => (U i).comp (R i)))
        (blockOperator B D hD hB - 1) := by
  let := separatedMetric o
  let VL : lp (fun i => Module (Q i) (E i)) 2 →ₗᵢ[ℂ] lp (fun i => Module (Q i) (G i)) 2 :=
    blockIsometry (fun i => coefficientIsometry (X := Q i) (L i))
  let VR : lp (fun i => Module (Q i) (F i)) 2 →ₗᵢ[ℂ] lp (fun i => Module (Q i) (G i)) 2 :=
    blockIsometry (fun i => coefficientIsometry (X := Q i) (R i))
  have hext : VL.toContinuousLinearMap.comp VL.toContinuousLinearMap.adjoint +
      VR.toContinuousLinearMap.comp VR.toContinuousLinearMap.adjoint = 1 :=
    blockIsometry_exhaustive _ _ (fun i => coefficientIsometry_exhaustive (L i) (R i) (hex i))
  have hb : blockOperator T K hK hT = operatorConjugation VL (blockOperator A C hC hA) +
      operatorConjugation VR (blockOperator B D hD hB) :=
    blockOperator_decomposition
      (fun i => coefficientIsometry (X := Q i) (L i))
      (fun i => coefficientIsometry (X := Q i) (R i))
      (fun i => coefficientIsometry_exhaustive (L i) (R i) (hex i))
      A B T C D K hC hD hK hA hB hT hL hR
  have hVL : (familyCoefficientIsometry U).comp VL =
      familyCoefficientIsometry (Q := Q) (fun i => (U i).comp (L i)) :=
    familyCoefficientIsometry_comp U L
  have hVR : (familyCoefficientIsometry U).comp VR =
      familyCoefficientIsometry (Q := Q) (fun i => (U i).comp (R i)) :=
    familyCoefficientIsometry_comp U R
  rw [coefficientFamilyMultiplier_value, hb]
  have h := isometricExtension_decomposition (familyCoefficientIsometry (Q := Q) U) VL VR hext
    (blockOperator A C hC hA) (blockOperator B D hD hB)
  simpa only [hVL, hVR] using h

end CoarseAssembly.DiscreteRoe

end

end OAI
