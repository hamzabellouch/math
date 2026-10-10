import OAI.Topology.CoarseAssembly.DiagonalSpatialFamily
import OAI.Topology.CoarseAssembly.FiniteCompactRoe

namespace OAI

/-! # Square defects of uniformly bounded component operators -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {V : ℕ → Type*} [∀ i, DecidableEq (V i)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [∀ i, DecidableEq (V i)] in
theorem squareDefect_norm_le (A : Operator (V 0) H) (C : ℝ) (hC : 0 ≤ C)
    (hA : ‖A‖ ≤ C) : ‖A * A - 1‖ ≤ C * C + 1 := by
  calc
    ‖A * A - 1‖ ≤ ‖A * A‖ + ‖(1 : Operator (V 0) H)‖ := norm_sub_le _ _
    _ ≤ (‖A‖ * ‖A‖) + 1 := add_le_add (norm_mul_le _ _) ContinuousLinearMap.norm_id_le
    _ ≤ C * C + 1 := by gcongr

omit [∀ i, DecidableEq (V i)] in
theorem diagonalFamily_square_defect (A : ∀ i, Operator (V i) H)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) :
    diagonalFamily A C hC hA * diagonalFamily A C hC hA - 1 =
      diagonalFamily (fun i => A i * A i - 1) (C * C + 1) (by positivity)
        (fun i => squareDefect_norm_le (V := fun _ => V i) (A i) C hC (hA i)) := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext z
  rcases z with ⟨i, x⟩
  simp only [sub_apply, mul_apply_eq_comp, one_apply_eq_self, lp.coeFn_sub, Pi.sub_apply,
    diagonalFamily_apply, rowVector_diagonalFamily]
  rfl

theorem diagonalFamily_square_compactEntries (A : ∀ i, Operator (V i) H)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
    (hsq : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (V i) H))) :
    CompactEntries (diagonalFamily A C hC hA * diagonalFamily A C hC hA - 1) := by
  rw [diagonalFamily_square_defect]
  rintro ⟨i, x⟩ ⟨j, y⟩
  by_cases hij : i = j
  · subst j
    rw [entry_diagonalFamily_same]
    exact compact_entries_of_compact (hsq i) x y
  · rw [entry_diagonalFamily_ne _ _ _ _ hij]
    exact isCompactOperator_zero

end CoarseAssembly.DiscreteRoe

end

end OAI
