import OAI.Topology.CoarseAssembly.MultiplierBoundaryNearby
import OAI.Topology.CoarseAssembly.DiagonalFamilyContinuity
import OAI.Topology.CoarseAssembly.SeparatedFamilyBoundary

namespace OAI

/-! # A uniform small perturbation preserves the whole-union boundary

The difference need not be compact. The argument uses the short invertible
path in the actual Roe unitization, with no componentwise K-theory inference.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem separatedFamilyBoundary_eq_of_nearby (o : ∀ i, Q i)
    (A B : ∀ i, Operator (Q i) H) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D)
    (r : ℝ) (hr : 0 ≤ r) (hpA : ∀ i, PropagationLE r (A i))
    (hpB : ∀ i, PropagationLE r (B i))
    (hsA : ∀ i, IsSelfAdjoint (A i)) (hsB : ∀ i, IsSelfAdjoint (B i))
    (hqA : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (Q i) H)))
    (hqB : ∀ i, IsCompactOperator (B i * B i - (1 : Operator (Q i) H)))
    (δ : ℝ) (hδ : 0 ≤ δ) (hδsmall : δ < 1 / 4)
    (hnear : ∀ i, ‖B i - A i‖ ≤ δ) :
    letI := separatedMetric o
    separatedFamilyBoundary o A C hC hA r hr hpA hsA hqA =
      separatedFamilyBoundary o B D hD hB r hr hpB hsB hqB := by
  let := separatedMetric o
  apply multiplierBoundaryClass_eq_of_nearby _ _
    (separatedFamilyMultiplier_selfAdjoint o A C hC hA r hr hpA hsA)
    (separatedFamilyMultiplier_selfAdjoint o B D hD hB r hr hpB hsB)
    (diagonalFamily_square_mem_roe o A C hC hA r hr hpA hsA hqA)
    (diagonalFamily_square_mem_roe o B D hD hB r hr hpB hsB hqB)
  exact (diagonalFamily_sub_norm_le B A D C hD hC hB hA δ hδ hnear).trans_lt hδsmall

end CoarseAssembly.DiscreteRoe

end

end OAI
