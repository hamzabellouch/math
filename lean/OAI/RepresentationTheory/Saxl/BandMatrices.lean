import OAI.RepresentationTheory.Saxl.PathAlternation

namespace OAI

noncomputable section

open scoped TensorProduct

universe uA

namespace Saxl.Band
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

def basis (i : ℕ) : Mat :=
  match i with
  | 0 => 1
  | 1 => !![1, 0; 0, -1]
  | 2 => !![0, 1; 1, 0]
  | _ => !![0, 1; -1, 0]

def D (q : ℕ) (X : Mat) : Mat := if q % 2 = 0 then X.adjugate else X

def segment (r p : ℕ) : Mat :=
  ∑ π : Equiv.Perm (Fin r),
    ((((Equiv.Perm.sign π) : ℤ) : ℂ)) •
      (List.ofFn (fun j : Fin r => D (p + j.val) (basis (π j).val))).prod

/- Consecutive segments with the original global position parities. -/
def blocks : ℕ → List ℕ → Mat
  | _, [] => 1
  | p, r :: rs => segment r p * blocks (p + r) rs

/- Enumeration of the finite symmetric group for the four small matrix calculations. -/
lemma sum_perm_succ {A : Type uA} [AddCommMonoid A] (n : ℕ)
    (f : Equiv.Perm (Fin (n + 1)) → A) :
    (∑ π, f π) = ∑ i : Fin (n + 1), ∑ σ : Equiv.Perm (Fin n),
      f (Equiv.Perm.decomposeFin.symm (i, σ)) := by
  calc
    (∑ π, f π) = ∑ x : Fin (n + 1) × Equiv.Perm (Fin n),
        f (Equiv.Perm.decomposeFin.symm x) :=
      Fintype.sum_equiv Equiv.Perm.decomposeFin _ _ (by intro π; simp)
    _ = _ := Fintype.sum_prod_type _

lemma decompose_apply_two {n : ℕ} (e : Equiv.Perm (Fin (n + 2))) (p : Fin (n + 3)) :
    Equiv.Perm.decomposeFin.symm (p, e) 2 = Equiv.swap 0 p (e 1).succ := by
  change Equiv.Perm.decomposeFin.symm (p, e) (1 : Fin (n + 2)).succ = _
  exact Equiv.Perm.decomposeFin_symm_apply_succ e p 1

lemma decompose_apply_three {n : ℕ} (e : Equiv.Perm (Fin (n + 3))) (p : Fin (n + 4)) :
    Equiv.Perm.decomposeFin.symm (p, e) 3 = Equiv.swap 0 p (e 2).succ := by
  change Equiv.Perm.decomposeFin.symm (p, e) (2 : Fin (n + 3)).succ = _
  exact Equiv.Perm.decomposeFin_symm_apply_succ e p 2

lemma segment_one_even : segment 1 0 = 1 := by
  simp [segment, List.ofFn_succ, basis, D]

lemma segment_one_odd : segment 1 1 = 1 := by
  simp [segment, List.ofFn_succ, basis, D]

lemma segment_two_even : segment 2 0 = (2 : ℂ) • basis 1 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff,
      Equiv.Perm.decomposeFin.symm_sign,
      Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

lemma segment_two_odd : segment 2 1 = (-2 : ℂ) • basis 1 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff,
      Equiv.Perm.decomposeFin.symm_sign,
      Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

lemma segment_three_even : segment 3 0 = (-6 : ℂ) • basis 3 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff,
      Equiv.Perm.decomposeFin.symm_sign,
      Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

lemma segment_three_odd : segment 3 1 = (-6 : ℂ) • basis 3 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff,
      Equiv.Perm.decomposeFin.symm_sign,
      Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

lemma segment_four_even : segment 4 0 = (24 : ℂ) • basis 0 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff,
      Equiv.Perm.decomposeFin.symm_sign,
      Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

lemma segment_four_odd : segment 4 1 = (-24 : ℂ) • basis 0 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff,
      Equiv.Perm.decomposeFin.symm_sign,
      Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

/- Only the original global parity matters. -/
lemma segment_mod (r p : ℕ) : segment r p = segment r (p % 2) := by
  simp [segment, D, Nat.add_mod]

def ScaledBasis (X : Mat) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ ∃ i : Fin 4, X = c • basis i.val

lemma scaledBasis_smul (c : ℂ) (hc : c ≠ 0) (i : Fin 4) :
    ScaledBasis (c • basis i.val) := ⟨c, hc, i, rfl⟩

lemma scaledBasis_one : ScaledBasis 1 := by
  exact ⟨1, one_ne_zero, 0, by simp [basis]⟩

lemma basis_mul (i j : Fin 4) : ScaledBasis (basis i.val * basis j.val) := by
  fin_cases i <;> fin_cases j
  · refine ⟨1, by norm_num, 0, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 3, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 0, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 3, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨-1, by norm_num, 3, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 0, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨-1, by norm_num, 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 3, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨-1, by norm_num, 2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨-1, by norm_num, 0, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]

lemma ScaledBasis.mul {X Y : Mat} (hX : ScaledBasis X) (hY : ScaledBasis Y) :
    ScaledBasis (X * Y) := by
  obtain ⟨c, hc, i, rfl⟩ := hX
  obtain ⟨d, hd, j, rfl⟩ := hY
  obtain ⟨e, he, k, hk⟩ := basis_mul i j
  refine ⟨c * d * e, mul_ne_zero (mul_ne_zero hc hd) he, k, ?_⟩
  rw [smul_mul_smul_comm, hk, smul_smul]

lemma segment_scaled (r p : ℕ) (hr : 1 ≤ r ∧ r ≤ 4) : ScaledBasis (segment r p) := by
  rw [segment_mod]
  have hp := Nat.mod_two_eq_zero_or_one p
  obtain ⟨hr1, hr4⟩ := hr
  interval_cases r <;> rcases hp with hp | hp <;> rw [hp]
  all_goals simp only [segment_one_even, segment_one_odd,
    segment_two_even, segment_two_odd, segment_three_even, segment_three_odd,
    segment_four_even, segment_four_odd]
  all_goals first
    | exact scaledBasis_one
    | exact scaledBasis_smul _ (by norm_num) 0
    | exact scaledBasis_smul _ (by norm_num) 1
    | exact scaledBasis_smul _ (by norm_num) 3

lemma blocks_scaled (rs : List ℕ) (hrs : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ 4) (p : ℕ) :
    ScaledBasis (blocks p rs) := by
  induction rs generalizing p with
  | nil => exact scaledBasis_one
  | cons r rs ih =>
    exact (segment_scaled r p (hrs r (by simp))).mul
      (ih (fun a ha => hrs a (by simp [ha])) (p + r))

def Q : Mat := !![1, 1; 1, 2]
def Qinv : Mat := !![2, -1; -1, 1]

lemma Q_mul_Qinv : Q * Qinv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Q, Qinv, Matrix.mul_apply, Fin.sum_univ_two]

lemma Qinv_mul_Q : Qinv * Q = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Q, Qinv, Matrix.mul_apply, Fin.sum_univ_two]

lemma Q_isUnit : IsUnit Q := ⟨⟨Q, Qinv, Q_mul_Qinv, Qinv_mul_Q⟩, rfl⟩

lemma Q_inverse : Q⁻¹ = Qinv := by
  exact Matrix.inv_eq_left_inv Qinv_mul_Q

lemma Q_basis_ne_zero (i : Fin 4) : (Q * basis i.val * Q⁻¹) 0 0 ≠ 0 := by
  rw [Q_inverse]
  fin_cases i <;> norm_num [Q, Qinv, basis, Matrix.mul_apply, Fin.sum_univ_two]

/- Endpoint noncancellation for arbitrary consecutive columns of lengths at most four. -/
theorem band_nonzero_pairing (rs : List ℕ)
    (hrs : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ 4) :
    ∃ Q : Mat, IsUnit Q ∧ (Q * blocks 1 rs * Q⁻¹) 0 0 ≠ 0 := by
  obtain ⟨c, hc, i, hi⟩ := blocks_scaled rs hrs 1
  refine ⟨Q, Q_isUnit, ?_⟩
  rw [hi, Matrix.mul_smul, Matrix.smul_mul]
  exact mul_ne_zero hc (Q_basis_ne_zero i)

end Saxl.Band

end

end OAI
