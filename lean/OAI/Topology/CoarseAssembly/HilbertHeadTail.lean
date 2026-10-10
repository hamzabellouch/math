import OAI.Topology.CoarseAssembly.CountableHilbertSum

namespace OAI

/-! # The head and tail decomposition used in finite-cycle telescoping -/

noncomputable section

namespace CoarseAssembly.Analytic

variable (H : ℕ → HilbertSpace)

def tailInsertVector (x : countableHilbertSpace (fun j => H (j + 1))) :
    countableHilbertSpace H :=
  ⟨(fun | 0 => 0 | j + 1 => x j), by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    apply (summable_nat_add_iff 1).mp
    exact l2_summable_sq x⟩

theorem tailInsertVector_norm (x : countableHilbertSpace (fun j => H (j + 1))) :
    ‖tailInsertVector H x‖ = ‖x‖ := by
  have he : ‖tailInsertVector H x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [l2_norm_sq, l2_norm_sq, (l2_summable_sq (tailInsertVector H x)).tsum_eq_zero_add]
    change ‖(0 : H 0)‖ ^ 2 + ∑' j, ‖x j‖ ^ 2 = ∑' j, ‖x j‖ ^ 2
    simp
  nlinarith [norm_nonneg x, norm_nonneg (tailInsertVector H x)]

def tailInsert : countableHilbertSpace (fun j => H (j + 1)) →ₗᵢ[ℂ] countableHilbertSpace H where
  toFun := tailInsertVector H
  map_add' x y := by
    apply lp.ext
    funext j
    cases j with
    | zero => change (0 : H 0) = 0 + 0; simp
    | succ j => rfl
  map_smul' z x := by
    apply lp.ext
    funext j
    cases j <;> simp [tailInsertVector]
  norm_map' := tailInsertVector_norm H

@[simp] theorem tailInsert_zero (x : countableHilbertSpace (fun j => H (j + 1))) :
    tailInsert H x 0 = 0 := rfl

@[simp] theorem tailInsert_succ (x : countableHilbertSpace (fun j => H (j + 1))) (j : ℕ) :
    tailInsert H x (j + 1) = x j := rfl

theorem tailInsert_single (j : ℕ) (y : H (j + 1)) :
    tailInsert H (lp.single 2 j y) = lp.single 2 (j + 1) y := by
  apply lp.ext
  funext k
  cases k with
  | zero => simp [tailInsert, tailInsertVector]
  | succ k =>
    by_cases hk : k = j
    · subst k
      simp [tailInsert, tailInsertVector, lp.single_apply]
    · simp [tailInsert, tailInsertVector, lp.single_apply, hk]

theorem tailInsert_adjoint_apply (x : countableHilbertSpace H) (j : ℕ) :
    (tailInsert H).toContinuousLinearMap.adjoint x j = x (j + 1) := by
  apply ext_inner_left ℂ
  intro y
  rw [← lp.inner_single_left (𝕜 := ℂ) (G := fun j => H (j + 1)),
    ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (tailInsert H (lp.single 2 j y)) x = inner ℂ y (x (j + 1))
  rw [tailInsert_single, lp.inner_single_left]

theorem head_tail_orthogonal :
    (summandIsometry H 0).toContinuousLinearMap.adjoint.comp
      (tailInsert H).toContinuousLinearMap = 0 := by
  rw [summandIsometry_adjoint]
  ext x
  rfl

theorem head_tail_exhaustive :
    (summandIsometry H 0).toContinuousLinearMap.comp
        (summandIsometry H 0).toContinuousLinearMap.adjoint +
      (tailInsert H).toContinuousLinearMap.comp (tailInsert H).toContinuousLinearMap.adjoint = 1 := by
  rw [summandIsometry_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext j
  change (lp.single (E := fun j => H j) 2 0 (x 0)) j +
    (tailInsert H ((tailInsert H).toContinuousLinearMap.adjoint x)) j = x j
  cases j with
  | zero =>
    rw [tailInsert_zero]
    simp
  | succ j =>
    rw [tailInsert_succ, tailInsert_adjoint_apply]
    simp

end CoarseAssembly.Analytic

end

end OAI
