import OAI.Topology.CoarseAssembly.ComponentHilbertInclusion
import OAI.Topology.CoarseAssembly.SeparatedFamilyBoundary
import OAI.Topology.CoarseAssembly.SpatialBoundaryNaturality

namespace OAI

/-! # Whole-union boundary naturality for component-preserving inclusions -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {Q P : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, MetricSpace (P i)]
  [∀ i, Fintype (Q i)] [∀ i, Fintype (P i)]
  [∀ i, DecidableEq (Q i)] [∀ i, DecidableEq (P i)]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem separatedFamilyBoundary_inclusion (o : ∀ i, Q i) (p : ∀ i, P i)
    (e : ∀ i, Q i ↪ P i)
    (he : letI := separatedMetric o; letI := separatedMetric p
      ∀ x y, dist (componentEmbedding e x) (componentEmbedding e y) ≤ dist x y)
    (A : ∀ i, Operator (Q i) H) (B : ∀ i, Operator (P i) H)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hp : ∀ i, PropagationLE r (A i)) (hq : ∀ i, PropagationLE s (B i))
    (hAs : ∀ i, IsSelfAdjoint (A i)) (hBs : ∀ i, IsSelfAdjoint (B i))
    (hAsq : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (Q i) H)))
    (hBsq : ∀ i, IsCompactOperator (B i * B i - (1 : Operator (P i) H)))
    (hAB : ∀ i, B i = isometricExtension (inclusionIsometry (e i)) (A i)) :
    letI := separatedMetric o
    letI := separatedMetric p
    OperatorKTheory.map (inclusionHom (X := Sigma Q) (Y := Sigma P) (H := H) (componentEmbedding e) he)
      (separatedFamilyBoundary o A C hC hA r hr hp hAs hAsq) =
        separatedFamilyBoundary p B D hD hB s hs hq hBs hBsq := by
  let := separatedMetric o
  let := separatedMetric p
  let F := separatedFamilyMultiplier o A C hC hA r hr hp
  let G := separatedFamilyMultiplier p B D hD hB s hs hq
  have hFs := separatedFamilyMultiplier_selfAdjoint o A C hC hA r hr hp hAs
  have hGs := separatedFamilyMultiplier_selfAdjoint p B D hD hB s hs hq hBs
  have hGF : G.val = isometricExtension (inclusionIsometry (componentEmbedding e)) F.val := by
    apply ContinuousLinearMap.ext
    intro v
    apply lp.ext
    funext z
    rcases z with ⟨i, x⟩
    have hh := congrArg (fun w : Module (P i) H => w x)
      (row_isometricExtension e (diagonalFamily A C hC hA) A
        (fun w j => rowVector_diagonalFamily A C hC hA w j) v i)
    change B i (rowVector v i) x = _
    rw [hAB i]
    exact hh.symm
  exact multiplierBoundaryClass_spatial (inclusionIsometry (componentEmbedding e))
    (inclusion_mapsToRoe (componentEmbedding e) he) F hFs
    (diagonalFamily_square_mem_roe o A C hC hA r hr hp hAs hAsq) G hGs
    (diagonalFamily_square_mem_roe p B D hD hB s hs hq hBs hBsq) hGF

end CoarseAssembly.DiscreteRoe

end

end OAI
