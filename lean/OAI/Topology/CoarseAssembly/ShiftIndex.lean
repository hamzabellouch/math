import OAI.Topology.CoarseAssembly.NegativeProjection

namespace OAI

/-! # The index-one compressed bilateral shift -/

noncomputable section

namespace CoarseAssembly.Analytic

def shiftToeplitz : End circleSequenceSpace := toeplitzCompression negativeProjection bilateralShift

def shiftToeplitzInverse : End circleSequenceSpace := toeplitzCompression negativeProjection (star bilateralShift)

theorem bilateralShift_star_apply (x : CircleSequence) (n : ℤ) :
    star bilateralShift x n = x (n + 1) := by
  have hs : star bilateralShift = (bilateralShiftEquiv.symm : CircleSequence →L[ℂ] CircleSequence) :=
    bilateralShiftEquiv.adjoint_eq_symm
  rw [hs]
  rfl

theorem shiftToeplitz_apply (x : CircleSequence) (n : ℤ) :
    shiftToeplitz x n = if n < 0 then x (n - 1) else x n := by
  change negativeProjection (bilateralShift (negativeProjection x)) n +
    (x n - negativeProjection x n) = _
  rw [negativeProjection_apply (bilateralShift (negativeProjection x)) n,
    bilateralShift_apply (negativeProjection x) n,
    negativeProjection_apply x (n - 1), negativeProjection_apply x n]
  split_ifs <;> simp_all
  all_goals omega

theorem shiftToeplitzInverse_apply (x : CircleSequence) (n : ℤ) :
    shiftToeplitzInverse x n = if n < 0 then (if n + 1 < 0 then x (n + 1) else 0) else x n := by
  change negativeProjection (star bilateralShift (negativeProjection x)) n +
    (x n - negativeProjection x n) = _
  rw [negativeProjection_apply (star bilateralShift (negativeProjection x)) n,
    bilateralShift_star_apply (negativeProjection x) n,
    negativeProjection_apply x (n + 1), negativeProjection_apply x n]
  split_ifs <;> simp_all

theorem shiftToeplitz_right_inverse : shiftToeplitz * shiftToeplitzInverse = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  change shiftToeplitz (shiftToeplitzInverse x) n = x n
  rw [shiftToeplitz_apply (shiftToeplitzInverse x) n]
  by_cases hn : n < 0
  · rw [ite_eq_left hn, shiftToeplitzInverse_apply x (n - 1),
      ite_eq_left (by omega : n - 1 < 0), ite_eq_left (by omega : n - 1 + 1 < 0)]
    rw [sub_add_cancel]
  · rw [ite_eq_right hn, shiftToeplitzInverse_apply x n, ite_eq_right hn]

theorem shiftToeplitz_surjective : Function.Surjective shiftToeplitz := by
  intro x
  refine ⟨shiftToeplitzInverse x, ?_⟩
  exact DFunLike.congr_fun shiftToeplitz_right_inverse x

/-- The kernel is exactly the last negative Fourier coordinate. -/
theorem shiftToeplitz_ker : shiftToeplitz.ker =
    Submodule.span ℂ {lp.single 2 (-1 : ℤ) (1 : ℂ)} := by
  apply le_antisymm
  · intro x hx
    have hz : shiftToeplitz x = 0 := hx
    apply Submodule.mem_span_singleton.mpr
    refine ⟨x (-1), ?_⟩
    apply lp.ext
    funext n
    by_cases hn : n = -1
    · subst n
      simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_apply_self, smul_eq_mul, mul_one]
    · have hx0 : x n = 0 := by
        by_cases hneg : n < 0
        · have hnn : n + 1 < 0 := by omega
          have h := congrArg (fun y : CircleSequence => y (n + 1)) hz
          rw [shiftToeplitz_apply x (n + 1), ite_eq_left hnn] at h
          simpa only [add_sub_cancel_right, lp.coeFn_zero, Pi.zero_apply] using h
        · have h := congrArg (fun y : CircleSequence => y n) hz
          rw [shiftToeplitz_apply x n, ite_eq_right hneg] at h
          exact h
      simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 (-1 : ℤ) (1 : ℂ) hn,
        smul_zero, hx0]
  · apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    change shiftToeplitz (lp.single 2 (-1 : ℤ) (1 : ℂ)) = 0
    apply lp.ext
    funext n
    rw [shiftToeplitz_apply]
    split_ifs with hn
    · exact lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 (-1 : ℤ) (1 : ℂ) (by omega)
    · exact lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 (-1 : ℤ) (1 : ℂ) (by omega)

theorem shiftToeplitz_index : shiftToeplitz.toLinearMap.index = 1 := by
  have he : (lp.single 2 (-1 : ℤ) (1 : ℂ) : CircleSequence) ≠ 0 := by
    intro h
    have h' := congrArg (fun x : CircleSequence => x (-1)) h
    have hzero : (1 : ℂ) = 0 := by
      simpa only [lp.single_apply_self, lp.coeFn_zero, Pi.zero_apply] using h'
    exact one_ne_zero hzero
  rw [LinearMap.index_eq_finrank_sub, shiftToeplitz_ker,
    LinearMap.range_eq_top.mpr shiftToeplitz_surjective]
  simp only [finrank_span_singleton he, Module.finrank_zero_of_subsingleton, Nat.cast_one,
    Nat.cast_zero, sub_zero]

end CoarseAssembly.Analytic

end

end OAI
