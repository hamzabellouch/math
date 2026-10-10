import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.CosetVertex

namespace OAI

namespace HarmonicArtin
universe u
variable {S : Type u}
open Matrix

theorem harmonic_positive_null_alternative {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hSym : ∀ i j, C i j = C j i)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (hConn : ∀ i j, Relation.ReflTransGen (fun a b => C a b < 0) i j)
    (v : ι → ℝ) (hv : ∀ i, 0 < v i) (hCv : ∀ i, 0 ≤ (C *ᵥ v) i) :
    C.PosDef ∨ C *ᵥ v = 0 := by
  by_cases hs : ∃ k, 0 < (C *ᵥ v) k
  · exact Or.inl (harmonic_posDef_of_strict_row C hSym hOff hConn v hv hCv hs)
  · right
    funext i
    exact le_antisymm (le_of_not_gt fun h => hs ⟨i, h⟩) (hCv i)

open scoped Classical

noncomputable def harmonicExtension {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (T : Set ι) (v : ι → ℝ) : ι → ℝ := by
  classical
  exact fun i => if hi : i ∈ T then
    ((C.submatrix Subtype.val Subtype.val : Matrix T T ℝ)⁻¹ *ᵥ
      fun a : T => ∑ b : ↥(Tᶜ), -(C a b) * v b) ⟨i, hi⟩ else v i

theorem harmonicExtension_outside {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (T : Set ι) (v : ι → ℝ) {i : ι} (hi : i ∉ T) :
    harmonicExtension C T v i = v i := by
  classical
  simp [harmonicExtension, hi]

theorem harmonicExtension_inside {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (T : Set ι) (v : ι → ℝ) :
    (fun i : T => harmonicExtension C T v i) =
      (C.submatrix Subtype.val Subtype.val : Matrix T T ℝ)⁻¹ *ᵥ
        (fun a : T => ∑ b : ↥(Tᶜ), -(C a b) * v b) := by
  classical
  funext i
  simp [harmonicExtension, i.property]

theorem harmonic_row_split {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (T : Set ι) (v : ι → ℝ) (i : ι) :
    (C *ᵥ v) i = (∑ j : T, C i j * v j) + ∑ j : ↥(Tᶜ), C i j * v j := by
  classical
  exact (Fintype.sum_subtype_add_sum_subtype (fun j => j ∈ T)
    (fun j => C i j * v j)).symm

theorem harmonicExtension_harmonic {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (T : Set ι)
    (hT : (C.submatrix Subtype.val Subtype.val : Matrix T T ℝ).PosDef)
    (v : ι → ℝ) (i : T) : (C *ᵥ harmonicExtension C T v) i = 0 := by
  classical
  rw [harmonic_row_split C T]
  have hsolve := congrFun (harmonic_solve
    (C.submatrix Subtype.val Subtype.val : Matrix T T ℝ) hT
    (fun a : T => ∑ b : ↥(Tᶜ), -(C a b) * v b)) i
  rw [← harmonicExtension_inside C T v] at hsolve
  change (∑ j : T, C i j * harmonicExtension C T v j) = _ at hsolve
  rw [hsolve]
  have he (j : ↥(Tᶜ)) : harmonicExtension C T v j = v j :=
    harmonicExtension_outside C T v j.property
  simp only [he, neg_mul, Finset.sum_neg_distrib, neg_add_cancel]

theorem harmonicExtension_nonneg {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (T : Set ι)
    (hT : (C.submatrix Subtype.val Subtype.val : Matrix T T ℝ).PosDef)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0) (v : ι → ℝ)
    (hv : ∀ i, 0 ≤ v i) : ∀ i, 0 ≤ harmonicExtension C T v i := by
  classical
  have hb (a : T) : 0 ≤ ∑ b : ↥(Tᶜ), -(C a b) * v b := by
    apply Finset.sum_nonneg
    intro b _
    have hab : (a : ι) ≠ b := fun h => b.property (h ▸ a.property)
    exact mul_nonneg (neg_nonneg.mpr (hOff a b hab)) (hv b)
  have hOffT (a b : T) (h : a ≠ b) : C a b ≤ 0 :=
    hOff a b (fun e => h (Subtype.ext e))
  intro i
  by_cases hi : i ∈ T
  · simpa only [harmonicExtension, dite_eq_left hi] using
      harmonic_extension_nonneg (C.submatrix Subtype.val Subtype.val : Matrix T T ℝ)
        hT hOffT _ hb ⟨i, hi⟩
  · simpa only [harmonicExtension_outside C T v hi] using hv i

theorem harmonic_solve_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.PosDef) (v : ι → ℝ) :
    C⁻¹ *ᵥ (C *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul C ((Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit),
    Matrix.one_mulVec]

theorem harmonicExtension_unique {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (T : Set ι)
    (hT : (C.submatrix Subtype.val Subtype.val : Matrix T T ℝ).PosDef)
    (v p : ι → ℝ) (hExt : ∀ i ∉ T, p i = v i)
    (hHarm : ∀ i : T, (C *ᵥ p) i = 0) : p = harmonicExtension C T v := by
  classical
  have hrow : (C.submatrix Subtype.val Subtype.val : Matrix T T ℝ) *ᵥ
      (fun i : T => p i) = fun a : T => ∑ b : ↥(Tᶜ), -(C a b) * v b := by
    funext i
    have hi := hHarm i
    rw [harmonic_row_split C T] at hi
    have he (j : ↥(Tᶜ)) : p j = v j := hExt j j.property
    simp only [he] at hi
    simp only [neg_mul, Finset.sum_neg_distrib]
    exact eq_neg_of_add_eq_zero_left hi
  have hval := harmonic_solve_left
    (C.submatrix Subtype.val Subtype.val : Matrix T T ℝ) hT (fun i : T => p i)
  rw [hrow, ← harmonicExtension_inside C T v] at hval
  funext i
  by_cases hi : i ∈ T
  · exact (congrFun hval ⟨i, hi⟩).symm
  · simpa only [harmonicExtension_outside C T v hi] using hExt i hi

theorem harmonic_upper_change {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (U : Set ι)
    (hU : (C.submatrix Subtype.val Subtype.val : Matrix U U ℝ).PosDef)
    (p q : ι → ℝ) (hExt : ∀ i ∉ U, q i = p i)
    (hHarm : ∀ i : U, (C *ᵥ q) i = 0) :
    (fun i : U => q i - p i) =
      -((C.submatrix Subtype.val Subtype.val : Matrix U U ℝ)⁻¹ *ᵥ
        fun i : U => (C *ᵥ p) i) := by
  classical
  have hrow : (C.submatrix Subtype.val Subtype.val : Matrix U U ℝ) *ᵥ
      (fun i : U => q i - p i) = -(fun i : U => (C *ᵥ p) i) := by
    funext i
    have hi := congrFun (Matrix.mulVec_sub C q p) (i : ι)
    simp only [Pi.sub_apply, hHarm i, zero_sub] at hi
    rw [harmonic_row_split C U] at hi
    have he : ∑ j : ↥(Uᶜ), C i j * (q - p) j = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp only [Pi.sub_apply, hExt j j.property, sub_self, mul_zero]
    rw [he, add_zero] at hi
    exact hi
  have hval := harmonic_solve_left
    (C.submatrix Subtype.val Subtype.val : Matrix U U ℝ) hU
    (fun i : U => q i - p i)
  rw [hrow, Matrix.mulVec_neg] at hval
  exact hval.symm

noncomputable def framedCartan (M : CoxeterMatrix S) :
    Matrix (S ⊕ Unit) (S ⊕ Unit) ℝ
  | .inl i, .inl j => if i = j then 2 else
      if M i j = 0 then -2 else -2 * Real.cos (Real.pi / (M i j : ℝ))
  | .inl _, .inr _ => -1
  | .inr _, .inl _ => -1
  | .inr _, .inr _ => 2

theorem framedCartan_symm (M : CoxeterMatrix S) (i j : S ⊕ Unit) :
    framedCartan M i j = framedCartan M j i := by
  cases i <;> cases j <;> simp only [framedCartan]
  rename_i i j
  by_cases h : i = j
  · subst j; simp
  · simp only [h, Ne.symm h, ↓reduceIte, M.symmetric i j]

theorem framedCartan_diag (M : CoxeterMatrix S) (i : S ⊕ Unit) :
    framedCartan M i i = 2 := by
  cases i <;> simp [framedCartan]

theorem framedCartan_off (M : CoxeterMatrix S) (i j : S ⊕ Unit) (h : i ≠ j) :
    framedCartan M i j ≤ 0 := by
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hij : i ≠ j := fun e => h (congrArg Sum.inl e)
      simp only [framedCartan, hij, ↓reduceIte]
      split_ifs with hm
      · norm_num
      · have hm2 : 2 ≤ M i j := by
          have hm1 := M.off_diagonal i j hij
          omega
        have hc : (2 : ℝ) ≤ (M i j : ℝ) := by exact_mod_cast hm2
        have hp : 0 < (M i j : ℝ) := by linarith
        have hcos : 0 ≤ Real.cos (Real.pi / (M i j : ℝ)) := by
          apply Real.cos_nonneg_of_mem_Icc
          constructor
          · have hn := div_nonneg Real.pi_pos.le hp.le
            linarith [Real.pi_pos]
          · apply (div_le_iff₀ hp).mpr
            nlinarith [Real.pi_pos]
        exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) hcos
    | inr j => norm_num [framedCartan]
  | inr i =>
    cases j with
    | inl j => norm_num [framedCartan]
    | inr j => exact (h (congrArg Sum.inr (Subsingleton.elim i j))).elim

theorem framedCartan_frame (M : CoxeterMatrix S) (i : S) :
    framedCartan M (.inl i) (.inr ()) = -1 := rfl

theorem harmonic_lower_change {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (R : Set ι)
    (hR : (C.submatrix Subtype.val Subtype.val : Matrix R R ℝ).PosDef)
    (p q : ι → ℝ) (hp : ∀ i : R, (C *ᵥ p) i = 0)
    (hq : ∀ i : R, (C *ᵥ q) i = 0) :
    (fun i : R => q i - p i) =
      (C.submatrix Subtype.val Subtype.val : Matrix R R ℝ)⁻¹ *ᵥ
        (fun i : R => ∑ j : ↥(Rᶜ), -(C i j) * (q j - p j)) := by
  have heq : q - p = harmonicExtension C R (q - p) := by
    apply harmonicExtension_unique C R hR
    · intro i _; rfl
    · intro i
      simp only [Matrix.mulVec_sub, Pi.sub_apply, hp i, hq i, sub_self]
  calc
    _ = (fun i : R => harmonicExtension C R (q - p) i) :=
      congrArg (fun v : ι → ℝ => fun i : R => v i) heq
    _ = _ := by
      simpa only [Pi.sub_apply] using harmonicExtension_inside C R (q - p)

theorem harmonic_boundary_comparison {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (R : Set ι)
    (hR : (C.submatrix Subtype.val Subtype.val : Matrix R R ℝ).PosDef)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (p q : ι → ℝ) (hp : ∀ i : R, (C *ᵥ p) i = 0)
    (hq : ∀ i : R, (C *ᵥ q) i = 0)
    (hext : ∀ i ∉ R, p i ≤ q i) : ∀ i, p i ≤ q i := by
  have hchange := harmonic_lower_change C R hR p q hp hq
  have hnonneg : ∀ i : R, 0 ≤ q i - p i := by
    intro a
    rw [congrFun hchange a]
    apply harmonic_extension_nonneg _ hR
    · intro i j hij
      exact hOff i j (fun e => hij (Subtype.ext e))
    · intro i
      apply Finset.sum_nonneg
      intro j _
      apply mul_nonneg
      · exact neg_nonneg.mpr (hOff i j (fun e => j.property (e ▸ i.property)))
      · exact sub_nonneg.mpr (hext j j.property)
  intro i
  by_cases hi : i ∈ R
  · exact sub_nonneg.mp (hnonneg ⟨i, hi⟩)
  · exact hext i hi

theorem harmonic_positive_neighbor_at {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) {i j : ι}
    (hCx : 0 ≤ (C *ᵥ x) i) (hij : C i j < 0) (hj : 0 < x j) : 0 < x i := by
  classical
  by_contra hi
  have hi0 : x i = 0 := le_antisymm (le_of_not_gt hi) (hx i)
  have hterm : ∀ k ∈ (Finset.univ : Finset ι), C i k * x k ≤ 0 := by
    intro k _
    by_cases hik : i = k
    · subst k; rw [hi0, mul_zero]
    · exact mul_nonpos_of_nonpos_of_nonneg (hOff i k hik) (hx k)
  have hsum : (C *ᵥ x) i < 0 :=
    Finset.sum_neg' hterm ⟨j, Finset.mem_univ j, mul_neg_of_neg_of_pos hij hj⟩
  exact (not_lt_of_ge hCx) hsum

theorem harmonic_support_alternative {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hSym : ∀ i j, C i j = C j i)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (G : Set ι)
    (hConn : ∀ i j : G, Relation.ReflTransGen (fun a b : G => C a b < 0) i j)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hrow : ∀ i : G, 0 ≤ (C *ᵥ p) i)
    (hInc : ∃ j, 0 < p j ∧ (j ∈ G ∨ ∃ i : G, C i j < 0)) :
    (C.submatrix Subtype.val Subtype.val : Matrix G G ℝ).PosDef ∨
      ((∀ i : G, 0 < p i) ∧ (∀ i : G, (C *ᵥ p) i = 0) ∧
        ∀ i : G, ∀ j ∉ G, C i j < 0 → p j = 0) := by
  classical
  let A : Matrix G G ℝ := C.submatrix Subtype.val Subtype.val
  have haOff (i j : G) (hij : i ≠ j) : A i j ≤ 0 :=
    hOff i j (fun h => hij (Subtype.ext h))
  have hext (i : G) : (∑ j : ↥(Gᶜ), C i j * p j) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    exact mul_nonpos_of_nonpos_of_nonneg
      (hOff i j (fun h => j.property (h ▸ i.property))) (hp j)
  have haRow (i : G) : 0 ≤ (A *ᵥ (fun j : G => p j)) i := by
    have hi := hrow i
    rw [harmonic_row_split C G] at hi
    have he := hext i
    change 0 ≤ ∑ j : G, C i j * p j
    linarith
  have hex : ∃ i : G, 0 < p i := by
    obtain ⟨j, hj, hjG | ⟨i, hij⟩⟩ := hInc
    · exact ⟨⟨j, hjG⟩, hj⟩
    · exact ⟨i, harmonic_positive_neighbor_at C hOff p hp (hrow i) hij hj⟩
  obtain ⟨j, hj⟩ := hex
  have hpG (i : G) : 0 < p i :=
    harmonic_positive_path A haOff (fun a : G => p a) (fun a => hp a)
      haRow (hConn i j) hj
  rcases harmonic_positive_null_alternative A (fun a b => hSym a b)
    haOff hConn (fun i : G => p i) hpG haRow with hdef | hnull
  · exact Or.inl hdef
  · right
    refine ⟨hpG, ?_, ?_⟩
    · intro i
      have hi := congrFun hnull i
      have ht := harmonic_row_split C G p i
      change (∑ j : G, C i j * p j) = 0 at hi
      rw [hi, zero_add] at ht
      exact le_antisymm (ht ▸ hext i) (hrow i)
    · intro i j hjG hij
      have hi := congrFun hnull i
      change (∑ j : G, C i j * p j) = 0 at hi
      have hr := hrow i
      rw [harmonic_row_split C G, hi, zero_add] at hr
      have hterm : ∀ b ∈ (Finset.univ : Finset ↥(Gᶜ)), C i b * p b ≤ 0 := by
        intro b _
        exact mul_nonpos_of_nonpos_of_nonneg
          (hOff i b (fun h => b.property (h ▸ i.property))) (hp b)
      have hz : C i j * p j = 0 :=
        (Finset.sum_eq_zero_iff_of_nonpos hterm).mp (le_antisymm (hext i) hr)
          ⟨j, hjG⟩ (Finset.mem_univ _)
      exact (mul_eq_zero.mp hz).resolve_left (ne_of_lt hij)

end HarmonicArtin

end OAI
