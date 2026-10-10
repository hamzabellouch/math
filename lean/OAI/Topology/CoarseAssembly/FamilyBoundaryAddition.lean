import OAI.Topology.CoarseAssembly.FamilyDecomposition

namespace OAI

/-! # Additivity of whole-union coefficient-family boundaries -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)]
  {E F G : ℕ → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)] [∀ i, CompleteSpace (F i)]
  [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℂ (G i)] [∀ i, CompleteSpace (G i)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem coefficientFamilyBoundary_add
    (o : ∀ i, Q i) (A : ∀ i, Operator (Q i) (E i)) (B : ∀ i, Operator (Q i) (F i))
    (T : ∀ i, Operator (Q i) (G i))
    (C D K : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D) (hT : ∀ i, ‖T i‖ ≤ K)
    (r : ℝ) (hr : 0 ≤ r)
    (hpA : ∀ i, PropagationLE r (A i)) (hpB : ∀ i, PropagationLE r (B i))
    (hpT : ∀ i, PropagationLE r (T i))
    (hsA : ∀ i, IsSelfAdjoint (A i)) (hsB : ∀ i, IsSelfAdjoint (B i)) (hsT : ∀ i, IsSelfAdjoint (T i))
    (hqA : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (Q i) (E i))))
    (hqB : ∀ i, IsCompactOperator (B i * B i - (1 : Operator (Q i) (F i))))
    (hqT : ∀ i, IsCompactOperator (T i * T i - (1 : Operator (Q i) (G i))))
    (L : ∀ i, E i →ₗᵢ[ℂ] G i) (R : ∀ i, F i →ₗᵢ[ℂ] G i)
    (hLR : ∀ i, (L i).toContinuousLinearMap.adjoint.comp (R i).toContinuousLinearMap = 0)
    (hex : ∀ i, (L i).toContinuousLinearMap.comp (L i).toContinuousLinearMap.adjoint +
      (R i).toContinuousLinearMap.comp (R i).toContinuousLinearMap.adjoint = 1)
    (hL : ∀ i, (T i).comp (coefficientIsometry (L i)).toContinuousLinearMap =
      (coefficientIsometry (L i)).toContinuousLinearMap.comp (A i))
    (hR : ∀ i, (T i).comp (coefficientIsometry (R i)).toContinuousLinearMap =
      (coefficientIsometry (R i)).toContinuousLinearMap.comp (B i))
    (U : ∀ i, G i →ₗᵢ[ℂ] H) :
    letI := separatedMetric o
    coefficientFamilyBoundary o T K hK hT r hr hpT hsT hqT U =
      coefficientFamilyBoundary o A C hC hA r hr hpA hsA hqA (fun i => (U i).comp (L i)) +
      coefficientFamilyBoundary o B D hD hB r hr hpB hsB hqB (fun i => (U i).comp (R i)) := by
  let := separatedMetric o
  let UL := fun i => (U i).comp (L i)
  let UR := fun i => (U i).comp (R i)
  let MT := coefficientFamilyMultiplier o T K hK hT r hr hpT U
  let MA := coefficientFamilyMultiplier o A C hC hA r hr hpA UL
  let MB := coefficientFamilyMultiplier o B D hD hB r hr hpB UR
  have hMTs := coefficientFamilyMultiplier_selfAdjoint o T K hK hT r hr hpT U hsT
  have hMAs := coefficientFamilyMultiplier_selfAdjoint o A C hC hA r hr hpA UL hsA
  have hMBs := coefficientFamilyMultiplier_selfAdjoint o B D hD hB r hr hpB UR hsB
  have hMTd := coefficientFamilyMultiplier_defect o T K hK hT r hr hpT U hsT hqT
  have hMAd := coefficientFamilyMultiplier_defect o A C hC hA r hr hpA UL hsA hqA
  have hMBd := coefficientFamilyMultiplier_defect o B D hD hB r hr hpB UR hsB hqB
  change multiplierBoundaryClass MT hMTs hMTd =
    multiplierBoundaryClass MA hMAs hMAd + multiplierBoundaryClass MB hMBs hMBd
  exact multiplierBoundaryClass_orthogonalEmbeddings
    (familyCoefficientIsometry UL) (familyCoefficientIsometry UR)
    (familyCoefficientIsometry_orthogonal U L R hLR)
    (blockOperator A C hC hA) (blockOperator B D hD hB)
    (blockOperator_selfAdjoint A C hC hA hsA) (blockOperator_selfAdjoint B D hD hB hsB)
    MT MA MB hMTs hMAs hMBs hMTd hMAd hMBd
    (coefficientFamilyMultiplier_value o A C hC hA r hr hpA UL)
    (coefficientFamilyMultiplier_value o B D hD hB r hr hpB UR)
    (coefficientFamilyMultiplier_decomposition_value o A B T C D K hC hD hK hA hB hT
      r hr hpT L R hex hL hR U)

end CoarseAssembly.DiscreteRoe

end

end OAI
