import OAI.Topology.CoarseAssembly.SeparatedFamilyBoundary
import OAI.Topology.CoarseAssembly.DiagonalFamilyContinuity
import OAI.Topology.CoarseAssembly.BoundaryRoePerturbation

namespace OAI

/-! # Compact changes on components give Roe perturbations on the whole union -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {V : ℕ → Type} [∀ i, MetricSpace (V i)] [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)] {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [∀ i, Fintype (V i)] in
theorem diagonalFamily_sub_mem_roe (o : ∀ i, V i)
    (A B : ∀ i, Operator (V i) H) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D)
    (r s : ℝ) (hr : 0 ≤ r) (_hs : 0 ≤ s)
    (hp : ∀ i, PropagationLE r (A i)) (hq : ∀ i, PropagationLE s (B i))
    (hAs : ∀ i, IsSelfAdjoint (A i)) (hBs : ∀ i, IsSelfAdjoint (B i))
    (hAB : ∀ i, IsCompactOperator (A i - B i)) :
    letI := separatedMetric o
    diagonalFamily A C hC hA - diagonalFamily B D hD hB ∈ algebra (X := Sigma V) (H := H) := by
  let := separatedMetric o
  have hn : ∀ i, ‖A i - B i‖ ≤ C + D := fun i =>
    (norm_sub_le _ _).trans (add_le_add (hA i) (hB i))
  rw [diagonalFamily_sub_eq A B C D hC hD hA hB (C + D) (add_nonneg hC hD) hn]
  let Q := diagonalFamily (fun i => A i - B i) (C + D) (add_nonneg hC hD) hn
  have hQp : PropagationLE (max r s) Q := by
    apply diagonalFamily_propagation o
    intro i
    have hneg : PropagationLE s (-B i) := by
      convert (hq i).smul (-1 : ℂ) using 1
      ext v
      simp
    simpa only [sub_eq_add_neg] using (hp i).add hneg
  have hQc : CompactEntries Q := by
    rintro ⟨i, x⟩ ⟨j, y⟩
    by_cases hij : i = j
    · subst j
      rw [entry_diagonalFamily_same]
      exact compact_entries_of_compact (hAB i) x y
    · rw [entry_diagonalFamily_ne _ _ _ _ hij]
      exact isCompactOperator_zero
  have hQs : IsSelfAdjoint Q :=
    diagonalFamily_selfAdjoint _ _ _ _ (fun i =>
      @IsSelfAdjoint.sub (Operator (V i) H) inferInstance inferInstance _ _ (hAs i) (hBs i))
  exact generator_mem ⟨⟨max r s, le_trans hr (le_max_left _ _), hQp⟩, hQc,
    by rwa [hQs.star_eq]⟩

/-- Componentwise compact changes preserve the whole-union class, even when
these compact operators do not tend to zero in norm. -/
theorem separatedFamilyBoundary_eq_of_component_compact (o : ∀ i, V i)
    (A B : ∀ i, Operator (V i) H) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hp : ∀ i, PropagationLE r (A i)) (hq : ∀ i, PropagationLE s (B i))
    (hAs : ∀ i, IsSelfAdjoint (A i)) (hBs : ∀ i, IsSelfAdjoint (B i))
    (hAsq : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (V i) H)))
    (hBsq : ∀ i, IsCompactOperator (B i * B i - (1 : Operator (V i) H)))
    (hAB : ∀ i, IsCompactOperator (A i - B i)) :
    letI := separatedMetric o
    separatedFamilyBoundary o A C hC hA r hr hp hAs hAsq =
      separatedFamilyBoundary o B D hD hB s hs hq hBs hBsq := by
  let := separatedMetric o
  have hdiff := diagonalFamily_sub_mem_roe o A B C D hC hD hA hB r s hr hs hp hq hAs hBs hAB
  have hrev : diagonalFamily B D hD hB - diagonalFamily A C hC hA ∈
      algebra (X := Sigma V) (H := H) := by
    have he : diagonalFamily B D hD hB - diagonalFamily A C hC hA =
        -(diagonalFamily A C hC hA - diagonalFamily B D hD hB) := by abel
    rw [he]
    exact (algebra (X := Sigma V) (H := H)).neg_mem hdiff
  exact multiplierBoundaryClass_roePerturbation
    (separatedFamilyMultiplier o A C hC hA r hr hp)
    (separatedFamilyMultiplier o B D hD hB s hs hq)
    (separatedFamilyMultiplier_selfAdjoint o A C hC hA r hr hp hAs)
    (separatedFamilyMultiplier_selfAdjoint o B D hD hB s hs hq hBs)
    (diagonalFamily_square_mem_roe o A C hC hA r hr hp hAs hAsq)
    (diagonalFamily_square_mem_roe o B D hD hB s hs hq hBs hBsq) hrev

end CoarseAssembly.DiscreteRoe

end

end OAI
