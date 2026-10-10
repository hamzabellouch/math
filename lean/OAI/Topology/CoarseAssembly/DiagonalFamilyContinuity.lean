import OAI.Topology.CoarseAssembly.DiagonalSpatialFamily

namespace OAI

/-! # Uniform component estimates give norm-continuous spatial families -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open Filter Topology

variable {V : ℕ → Type*} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem diagonalFamily_sub_eq (A B : ∀ i, Operator (V i) H)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D)
    (δ : ℝ) (hδ : 0 ≤ δ) (hAB : ∀ i, ‖A i - B i‖ ≤ δ) :
    diagonalFamily A C hC hA - diagonalFamily B D hD hB =
      diagonalFamily (fun i => A i - B i) δ hδ hAB := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext z
  rcases z with ⟨i, x⟩
  simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, diagonalFamily_apply]

/-- The bound does not depend on the number or sizes of the components. -/
theorem diagonalFamily_sub_norm_le (A B : ∀ i, Operator (V i) H)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D)
    (δ : ℝ) (hδ : 0 ≤ δ) (hAB : ∀ i, ‖A i - B i‖ ≤ δ) :
    ‖diagonalFamily A C hC hA - diagonalFamily B D hD hB‖ ≤ δ := by
  rw [diagonalFamily_sub_eq A B C D hC hD hA hB δ hδ hAB]
  exact diagonalFamily_norm_le _ _ _ _

theorem continuous_diagonalFamily {P : Type*} [TopologicalSpace P]
    (A : P → ∀ i, Operator (V i) H) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ p i, ‖A p i‖ ≤ C)
    (hcont : ∀ p ε, 0 < ε → ∀ᶠ q in 𝓝 p, ∀ i, ‖A q i - A p i‖ ≤ ε) :
    Continuous (fun p => diagonalFamily (A p) C hC (hA p)) := by
  rw [continuous_iff_continuousAt]
  intro p
  apply (Metric.continuousAt_iff'
    (f := fun q : P => (diagonalFamily (A q) C hC (hA q) : Operator (Sigma V) H))).mpr
  intro ε hε
  filter_upwards [hcont p (ε / 2) (half_pos hε)] with q hq
  rw [dist_eq_norm (diagonalFamily (A q) C hC (hA q))
    (diagonalFamily (A p) C hC (hA p))]
  exact (diagonalFamily_sub_norm_le (A q) (A p) C C hC hC (hA q) (hA p)
    (ε / 2) (le_of_lt (half_pos hε)) hq).trans_lt (half_lt_self hε)

end CoarseAssembly.DiscreteRoe

end

end OAI
