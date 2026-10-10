import OAI.Topology.CoarseAssembly.SeparatedFamilyBoundary

namespace OAI

/-! # A boundary class does not depend on its norm or propagation certificate -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem separatedFamilyBoundary_bound_independent (o : ∀ i, Q i)
    (A : ∀ i, Operator (Q i) H) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖A i‖ ≤ D)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hp : ∀ i, PropagationLE r (A i)) (hq : ∀ i, PropagationLE s (A i))
    (hself : ∀ i, IsSelfAdjoint (A i))
    (hsq : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (Q i) H))) :
    letI := separatedMetric o
    separatedFamilyBoundary o A C hC hA r hr hp hself hsq =
      separatedFamilyBoundary o A D hD hB s hs hq hself hsq := by
  let := separatedMetric o
  have he : separatedFamilyMultiplier o A C hC hA r hr hp =
      separatedFamilyMultiplier o A D hD hB s hs hq := by
    apply Subtype.ext
    ext v p
    rcases p with ⟨i, x⟩
    rfl
  unfold separatedFamilyBoundary
  simp only [he]

theorem separatedFamilyBoundary_congr (o : ∀ i, Q i)
    (A B : ∀ i, Operator (Q i) H) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hp : ∀ i, PropagationLE r (A i)) (hq : ∀ i, PropagationLE s (B i))
    (hselfA : ∀ i, IsSelfAdjoint (A i)) (hselfB : ∀ i, IsSelfAdjoint (B i))
    (hsqA : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (Q i) H)))
    (hsqB : ∀ i, IsCompactOperator (B i * B i - (1 : Operator (Q i) H)))
    (hAB : A = B) :
    letI := separatedMetric o
    separatedFamilyBoundary o A C hC hA r hr hp hselfA hsqA =
      separatedFamilyBoundary o B D hD hB s hs hq hselfB hsqB := by
  subst B
  exact separatedFamilyBoundary_bound_independent o A C D hC hD hA hB r s hr hs hp hq hselfA hsqA

end CoarseAssembly.DiscreteRoe

end

end OAI
