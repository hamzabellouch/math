import OAI.Topology.CoarseAssembly.HilbertSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace OAI

/-! # Bounded operators from controlled block matrices

A finite-propagation matrix has uniformly bounded row and column supports.
Cauchy--Schwarz and finite double counting construct its bounded operator
directly. This supplies the boundedness step of the transfer lift without
an auxiliary edge colouring.
-/

noncomputable section

namespace CoarseAssembly

open scoped BigOperators

theorem norm_sum_sq_le_card {J E : Type*} [NormedAddCommGroup E]
    (s : Finset J) (x : J → E) :
    ‖∑ j ∈ s, x j‖ ^ 2 ≤ (s.card : ℝ) * ∑ j ∈ s, ‖x j‖ ^ 2 := by
  have hn := norm_sum_le s x
  have hs := Finset.sum_mul_sq_le_sq_mul_sq s (fun j => ‖x j‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  have hnon : 0 ≤ ∑ j ∈ s, ‖x j‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  calc
    _ ≤ (∑ j ∈ s, ‖x j‖) ^ 2 := by nlinarith [norm_nonneg (∑ j ∈ s, x j)]
    _ ≤ _ := by simpa only [mul_comm] using hs

variable {I : Type*} [DecidableEq I]

theorem sum_neighbors_le (rows cols : I → Finset I)
    (hdual : ∀ i j, j ∈ rows i ↔ i ∈ cols j) (N : ℕ)
    (hc : ∀ j, (cols j).card ≤ N) (S : Finset I) (f : I → ℝ)
    (hf : ∀ j, 0 ≤ f j) :
    ∑ i ∈ S, ∑ j ∈ rows i, f j ≤ (N : ℝ) * ∑ j ∈ S.biUnion rows, f j := by
  let T := S.biUnion rows
  have heq : (∑ i ∈ S, ∑ j ∈ rows i, f j) =
      ∑ j ∈ T, ((S.filter (fun i => j ∈ rows i)).card : ℝ) * f j := by
    calc
      _ = ∑ i ∈ S, ∑ j ∈ T, if j ∈ rows i then f j else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          _ = ∑ j ∈ rows i, if j ∈ rows i then f j else 0 := by simp
          _ = _ := Finset.sum_subset
            (fun j hj => Finset.mem_biUnion.mpr ⟨i, hi, hj⟩)
            (by intro j hj hjnot; simp [hjnot])
      _ = ∑ j ∈ T, ∑ i ∈ S, if j ∈ rows i then f j else 0 := Finset.sum_comm
      _ = _ := by simp [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [heq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_right _ (hf j)
  exact_mod_cast (Finset.card_le_card (show S.filter (fun i => j ∈ rows i) ⊆ cols j from
    fun i hi => (hdual i j).mp (Finset.mem_filter.mp hi).2)).trans (hc j)

variable {E : I → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]

def matrixRow (rows : I → Finset I) (A : ∀ i j, E j →L[ℂ] E i)
    (x : lp E 2) (i : I) : E i := ∑ j ∈ rows i, A i j (x j)

omit [DecidableEq I] in
theorem matrixRow_norm_sq (rows : I → Finset I) (A : ∀ i j, E j →L[ℂ] E i)
    (N : ℕ) (C : ℝ) (_hC : 0 ≤ C) (hr : ∀ i, (rows i).card ≤ N)
    (hA : ∀ i j, j ∈ rows i → ‖A i j‖ ≤ C) (x : lp E 2) (i : I) :
    ‖matrixRow rows A x i‖ ^ 2 ≤ (N : ℝ) * C ^ 2 * ∑ j ∈ rows i, ‖x j‖ ^ 2 := by
  have hentry (j : I) (hj : j ∈ rows i) : ‖A i j (x j)‖ ≤ C * ‖x j‖ :=
    (A i j).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hA i j hj) (norm_nonneg _))
  calc
    _ ≤ ((rows i).card : ℝ) * ∑ j ∈ rows i, ‖A i j (x j)‖ ^ 2 :=
      norm_sum_sq_le_card _ _
    _ ≤ (N : ℝ) * ∑ j ∈ rows i, (C * ‖x j‖) ^ 2 := by
      refine mul_le_mul (by exact_mod_cast hr i) ?_
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg N)
      apply Finset.sum_le_sum
      intro j hj
      gcongr
      exact hentry j hj
    _ = _ := by simp only [mul_pow, ← Finset.mul_sum]; ring

theorem matrix_finite_norm_sq (rows cols : I → Finset I)
    (hdual : ∀ i j, j ∈ rows i ↔ i ∈ cols j) (A : ∀ i j, E j →L[ℂ] E i)
    (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hr : ∀ i, (rows i).card ≤ N) (hc : ∀ i, (cols i).card ≤ N)
    (hA : ∀ i j, j ∈ rows i → ‖A i j‖ ≤ C) (x : lp E 2) (S : Finset I) :
    ∑ i ∈ S, ‖matrixRow rows A x i‖ ^ 2 ≤ ((N : ℝ) * C * ‖x‖) ^ 2 := by
  calc
    _ ≤ ∑ i ∈ S, (N : ℝ) * C ^ 2 * ∑ j ∈ rows i, ‖x j‖ ^ 2 :=
      Finset.sum_le_sum (fun i _ => matrixRow_norm_sq rows A N C hC hr hA x i)
    _ = (N : ℝ) * C ^ 2 * ∑ i ∈ S, ∑ j ∈ rows i, ‖x j‖ ^ 2 :=
      (Finset.mul_sum ..).symm
    _ ≤ (N : ℝ) * C ^ 2 * ((N : ℝ) * ∑ j ∈ S.biUnion rows, ‖x j‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left (sum_neighbors_le rows cols hdual N hc S
        (fun j => ‖x j‖ ^ 2) (fun _ => sq_nonneg _)) (by positivity)
    _ ≤ (N : ℝ) * C ^ 2 * ((N : ℝ) * ‖x‖ ^ 2) := by
      gcongr
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) x (S.biUnion rows)
    _ = _ := by ring

def controlledMatrixLinear (rows cols : I → Finset I)
    (hdual : ∀ i j, j ∈ rows i ↔ i ∈ cols j) (A : ∀ i j, E j →L[ℂ] E i)
    (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hr : ∀ i, (rows i).card ≤ N) (hc : ∀ i, (cols i).card ≤ N)
    (hA : ∀ i j, j ∈ rows i → ‖A i j‖ ≤ C) : lp E 2 →ₗ[ℂ] lp E 2 where
  toFun x := ⟨matrixRow rows A x, by
    apply memℓp_gen'
    intro S
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      matrix_finite_norm_sq rows cols hdual A N C hC hr hc hA x S⟩
  map_add' x y := by
    apply lp.ext
    funext i
    change (∑ j ∈ rows i, A i j (x j + y j)) =
      (∑ j ∈ rows i, A i j (x j)) + ∑ j ∈ rows i, A i j (y j)
    simp only [map_add, Finset.sum_add_distrib]
  map_smul' c x := by
    apply lp.ext
    funext i
    simp [matrixRow, map_smul, Finset.smul_sum]

theorem controlledMatrixLinear_norm_le (rows cols : I → Finset I)
    (hdual : ∀ i j, j ∈ rows i ↔ i ∈ cols j) (A : ∀ i j, E j →L[ℂ] E i)
    (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hr : ∀ i, (rows i).card ≤ N) (hc : ∀ i, (cols i).card ≤ N)
    (hA : ∀ i j, j ∈ rows i → ‖A i j‖ ≤ C) (x : lp E 2) :
    ‖controlledMatrixLinear rows cols hdual A N C hC hr hc hA x‖ ≤ (N : ℝ) * C * ‖x‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num) (by positivity)
  intro S
  change (∑ i ∈ S, ‖matrixRow rows A x i‖ ^ (2 : ENNReal).toReal) ≤
    ((N : ℝ) * C * ‖x‖) ^ (2 : ENNReal).toReal
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    matrix_finite_norm_sq rows cols hdual A N C hC hr hc hA x S

def controlledMatrix (rows cols : I → Finset I)
    (hdual : ∀ i j, j ∈ rows i ↔ i ∈ cols j) (A : ∀ i j, E j →L[ℂ] E i)
    (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hr : ∀ i, (rows i).card ≤ N) (hc : ∀ i, (cols i).card ≤ N)
    (hA : ∀ i j, j ∈ rows i → ‖A i j‖ ≤ C) : lp E 2 →L[ℂ] lp E 2 :=
  (controlledMatrixLinear rows cols hdual A N C hC hr hc hA).mkContinuous ((N : ℝ) * C)
    (controlledMatrixLinear_norm_le rows cols hdual A N C hC hr hc hA)

theorem controlledMatrix_norm_le (rows cols : I → Finset I)
    (hdual : ∀ i j, j ∈ rows i ↔ i ∈ cols j) (A : ∀ i j, E j →L[ℂ] E i)
    (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hr : ∀ i, (rows i).card ≤ N) (hc : ∀ i, (cols i).card ≤ N)
    (hA : ∀ i j, j ∈ rows i → ‖A i j‖ ≤ C) :
    ‖controlledMatrix rows cols hdual A N C hC hr hc hA‖ ≤ (N : ℝ) * C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact controlledMatrixLinear_norm_le rows cols hdual A N C hC hr hc hA

@[simp] theorem controlledMatrix_apply (rows cols : I → Finset I)
    (hdual : ∀ i j, j ∈ rows i ↔ i ∈ cols j) (A : ∀ i j, E j →L[ℂ] E i)
    (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hr : ∀ i, (rows i).card ≤ N) (hc : ∀ i, (cols i).card ≤ N)
    (hA : ∀ i j, j ∈ rows i → ‖A i j‖ ≤ C) (x : lp E 2) (i : I) :
    controlledMatrix rows cols hdual A N C hC hr hc hA x i = ∑ j ∈ rows i, A i j (x j) := rfl

end CoarseAssembly

end

end OAI
