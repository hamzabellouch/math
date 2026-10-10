import OAI.Topology.CoarseAssembly.CountableHilbertSum

namespace OAI

/-! # Reindexing repeated Hilbert summands for finite telescoping -/

noncomputable section

namespace CoarseAssembly.Analytic

variable (H : HilbertSpace)

abbrev repeatedHilbert := countableHilbertSpace (fun _ : ℕ => H)

def reindexRepeated (e : ℕ ≃ ℕ) (x : repeatedHilbert H) : repeatedHilbert H :=
  ⟨fun j => x (e.symm j), by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    exact e.symm.summable_iff.mpr (l2_summable_sq x)⟩

theorem reindexRepeated_norm (e : ℕ ≃ ℕ) (x : repeatedHilbert H) :
    ‖reindexRepeated H e x‖ = ‖x‖ := by
  have he : ‖reindexRepeated H e x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [l2_norm_sq, l2_norm_sq]
    exact e.symm.tsum_eq (fun j => ‖x j‖ ^ 2)
  nlinarith [norm_nonneg x, norm_nonneg (reindexRepeated H e x)]

def repeatedReindexEquiv (e : ℕ ≃ ℕ) : repeatedHilbert H ≃ₗᵢ[ℂ] repeatedHilbert H where
  toFun := reindexRepeated H e
  invFun := reindexRepeated H e.symm
  left_inv x := by apply lp.ext; funext j; simp [reindexRepeated]
  right_inv x := by apply lp.ext; funext j; simp [reindexRepeated]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' := reindexRepeated_norm H e

theorem blockOperator_reindex (e : ℕ ≃ ℕ) (T : ℕ → End H)
    (C : ℝ) (hC : 0 ≤ C) (hT : ∀ j, ‖T j‖ ≤ C) :
    operatorConjugation (repeatedReindexEquiv H e).toLinearIsometry
      (blockOperator T C hC hT) =
    blockOperator (fun j => T (e.symm j)) C hC (fun j => hT (e.symm j)) := by
  have hadj : (repeatedReindexEquiv H e).toLinearIsometry.toContinuousLinearMap.adjoint =
      (repeatedReindexEquiv H e).symm.toLinearIsometry.toContinuousLinearMap :=
    (repeatedReindexEquiv H e).adjoint_eq_symm
  change (repeatedReindexEquiv H e).toLinearIsometry.toContinuousLinearMap.comp
      ((blockOperator T C hC hT).comp (repeatedReindexEquiv H e).toLinearIsometry.toContinuousLinearMap.adjoint) = _
  rw [hadj]
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext j
  change T (e.symm j) (x (e (e.symm j))) = T (e.symm j) (x j)
  rw [e.apply_symm_apply]

/-- Rotate the first `N+1` coordinates, leaving the infinite tail fixed. -/
def rotatePrefix (N : ℕ) : ℕ ≃ ℕ where
  toFun j := if j = 0 then N else if j ≤ N then j - 1 else j
  invFun j := if j < N then j + 1 else if j = N then 0 else j
  left_inv j := by
    dsimp only
    by_cases h0 : j = 0
    · subst j
      simp
    by_cases hj : j ≤ N
    · have hlt : j - 1 < N := by omega
      simp only [ite_eq_right h0, ite_eq_left hj, ite_eq_left hlt]
      omega
    · have hnj : ¬j < N := by omega
      have hne : j ≠ N := by omega
      simp [h0, hj, hnj, hne]
  right_inv j := by
    dsimp only
    by_cases hj : j < N
    · have hle : j + 1 ≤ N := by omega
      simp [hj, hle]
    · by_cases he : j = N
      · subst j
        simp
      · have h0 : j ≠ 0 := by omega
        have hle : ¬j ≤ N := by omega
        simp [hj, he, h0, hle]

@[simp] theorem rotatePrefix_zero (N : ℕ) : rotatePrefix N 0 = N := by simp [rotatePrefix]

theorem rotatePrefix_inverse_lt (N j : ℕ) (hj : j < N) :
    (rotatePrefix N).symm j = j + 1 := by simp [rotatePrefix, hj]

@[simp] theorem rotatePrefix_inverse_last (N : ℕ) : (rotatePrefix N).symm N = 0 := by
  simp [rotatePrefix]

theorem rotatePrefix_inverse_gt (N j : ℕ) (hj : N < j) :
    (rotatePrefix N).symm j = j := by
  simp [rotatePrefix, not_lt.mpr hj.le, ne_of_gt hj]

end CoarseAssembly.Analytic

end

end OAI
