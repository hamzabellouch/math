import Mathlib
import OAI.RepresentationTheory.RestrictedTilting.CharacterExpansions

namespace OAI

/-! Binary weight bases and upper and lower unipotent degree bounds. -/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace FiberFunctorProof
section

universe u
variable (k : Type u) [Field k]

 

noncomputable def binaryExponentEquiv (n : ℕ) :
    {d : Fin 2 →₀ ℕ // Finsupp.degree d = n} ≃ Fin (n + 1) where
  toFun d := ⟨d.val 1, by
    have hd := d.property
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hd
    omega⟩
  invFun i := ⟨Finsupp.single (0 : Fin 2) (n - (i : ℕ)) + Finsupp.single (1 : Fin 2) (i : ℕ), by
    simp only [map_add, Finsupp.degree_single]
    omega⟩
  left_inv d := by
    apply Subtype.ext
    have hd := d.property
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hd
    ext i
    fin_cases i <;> simp
    omega
  right_inv i := by
    apply Fin.ext
    simp

noncomputable def homogeneousMonomialBasis (n : ℕ) :
    Module.Basis {d : Fin 2 →₀ ℕ // Finsupp.degree d = n} k
      (MvPolynomial.homogeneousSubmodule (Fin 2) k n) :=
  (MvPolynomial.basisRestrictSupport k {d : Fin 2 →₀ ℕ | Finsupp.degree d = n}).map
    (LinearEquiv.ofEq _ _ (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported
      (Fin 2) k n).symm)

noncomputable def binaryBasis (n : ℕ) : Module.Basis (Fin (n + 1)) k
    (MvPolynomial.homogeneousSubmodule (Fin 2) k n) :=
  (homogeneousMonomialBasis k n).reindex (binaryExponentEquiv n)

lemma homogeneousMonomialBasis_apply (n : ℕ)
    (d : {d : Fin 2 →₀ ℕ // Finsupp.degree d = n}) :
    ((homogeneousMonomialBasis k n d).val : MvPolynomial (Fin 2) k) =
      MvPolynomial.monomial d.val 1 := by
  change AddMonoidAlgebra.ofCoeff
    (((Finsupp.supportedEquivFinsupp (R := k)
      {d : Fin 2 →₀ ℕ | Finsupp.degree d = n}).symm (Finsupp.single d 1)).val) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

lemma binaryBasis_apply (n : ℕ) (i : Fin (n + 1)) :
    (binaryBasis k n i).val =
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ (n - i) * MvPolynomial.X 1 ^ (i : ℕ) := by
  rw [binaryBasis, Module.Basis.reindex_apply, homogeneousMonomialBasis_apply]
  change MvPolynomial.monomial (Finsupp.single (0 : Fin 2) (n - (i : ℕ)) + Finsupp.single (1 : Fin 2) (i : ℕ)) 1 = _
  rw [← one_mul (1 : k), ← MvPolynomial.monomial_mul_monomial]
  simp [MvPolynomial.X_pow_eq_monomial]

lemma binaryBasis_finrank (n : ℕ) :
    Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin 2) k n) = n + 1 := by
  simpa using Module.finrank_eq_card_basis (binaryBasis k n)


lemma dualMatrix_diagonal (a : kˣ) : dualMatrix k (diagonalTorus k a) =
    !![(↑a⁻¹ : k), 0; 0, (a : k)] := by
  change (((diagonalTorus k a)⁻¹ : SL2 k) : Matrix (Fin 2) (Fin 2) k).transpose = _
  rw [← map_inv]
  change (!![(↑a⁻¹ : k), 0; 0, (↑(a⁻¹)⁻¹ : k)] : Matrix (Fin 2) (Fin 2) k).transpose = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma linearChange_diagonal_X0 (a : kˣ) :
    linearChange (dualMatrix k (diagonalTorus k a)) (MvPolynomial.X 0) =
      MvPolynomial.C (↑a⁻¹ : k) * MvPolynomial.X 0 := by
  rw [dualMatrix_diagonal, linearChange_X]
  simp [Fin.sum_univ_two]

lemma linearChange_diagonal_X1 (a : kˣ) :
    linearChange (dualMatrix k (diagonalTorus k a)) (MvPolynomial.X 1) =
      MvPolynomial.C (a : k) * MvPolynomial.X 1 := by
  rw [dualMatrix_diagonal, linearChange_X]
  simp [Fin.sum_univ_two]

 
lemma costandard_basis_weight (n : ℕ) (i : Fin (n + 1)) (a : kˣ) :
    (costandard k n).ρ (diagonalTorus k a) (binaryBasis k n i) =
      integerCharacter k (2 * (i : ℤ) - n) a • binaryBasis k n i := by
  apply Subtype.ext
  change linearChange (dualMatrix k (diagonalTorus k a)) (binaryBasis k n i).val = _
  rw [binaryBasis_apply]
  simp only [map_mul, map_pow, linearChange_diagonal_X0, linearChange_diagonal_X1,
    Submodule.coe_smul_of_tower, binaryBasis_apply, MvPolynomial.smul_eq_C_mul]
  have hscalar : (↑a⁻¹ : k) ^ (n - (i : ℕ)) * (a : k) ^ (i : ℕ) =
      integerCharacter k (2 * (i : ℤ) - n) a := by
    change ((a⁻¹ ^ (n - (i : ℕ)) * a ^ (i : ℕ) : kˣ) : k) =
      ((a ^ (2 * (i : ℤ) - n) : kˣ) : k)
    congr 1
    simp only [← zpow_natCast, inv_zpow, ← zpow_neg, ← zpow_add]
    congr 1
    have hi := i.isLt
    omega
  calc
    ((MvPolynomial.C (↑a⁻¹ : k) : MvPolynomial (Fin 2) k) * MvPolynomial.X 0) ^ (n - (i : ℕ)) *
        (MvPolynomial.C (a : k) * MvPolynomial.X 1) ^ (i : ℕ) =
      MvPolynomial.C ((↑a⁻¹ : k) ^ (n - (i : ℕ)) * (a : k) ^ (i : ℕ)) *
        (MvPolynomial.X 0 ^ (n - (i : ℕ)) * MvPolynomial.X 1 ^ (i : ℕ)) := by
      simp only [mul_pow, map_mul, map_pow]
      ring
    _ = _ := by rw [hscalar]

 
lemma eigenvector_eq_zero_of_basis {M : Type*} [AddCommGroup M] [Module k M]
    {I : Type*} [Fintype I] (b : Module.Basis I k M) (w : I → ℤ)
    (ρ : Representation k (SL2 k) M)
    (hb : ∀ i a, ρ (diagonalTorus k a) (b i) = integerCharacter k (w i) a • b i)
    [Infinite k] (n : ℤ) (hn : ∀ i, n ≠ w i) (v : M)
    (hv : ∀ a, ρ (diagonalTorus k a) v = integerCharacter k n a • v) : v = 0 := by
  classical
  apply b.repr.injective
  ext i
  simp only [map_zero, Finsupp.zero_apply]
  by_contra hc
  have heq : integerCharacter k n = integerCharacter k (w i) := by
    ext a
    have hcoord : (b.coord i).comp (ρ (diagonalTorus k a)) =
        integerCharacter k (w i) a • b.coord i := by
      apply b.ext
      intro j
      simp only [LinearMap.comp_apply, hb, map_smul, Module.Basis.coord_apply,
        Module.Basis.repr_self, Finsupp.single_apply, LinearMap.smul_apply, smul_eq_mul]
      split_ifs with hji
      · subst j; rfl
      · simp
    have hv' := congrArg (b.coord i) (hv a)
    rw [← LinearMap.comp_apply, hcoord] at hv'
    simp only [LinearMap.smul_apply, Module.Basis.coord_apply, map_smul, smul_eq_mul] at hv'
    exact (mul_right_cancel₀ hc hv').symm
  exact hn i (integerCharacter_injective k heq)

 

lemma costandard_weight_bound [Infinite k] (n : ℕ) (m : ℤ)
    (hm : m < -(n : ℤ) ∨ (n : ℤ) < m)
    (v : costandard k n) (hv : ∀ a,
      (costandard k n).ρ (diagonalTorus k a) v = integerCharacter k m a • v) : v = 0 := by
  apply eigenvector_eq_zero_of_basis k (binaryBasis k n) (fun i => 2 * (i : ℤ) - n)
    (costandard k n).ρ (costandard_basis_weight k n) m ?_ v hv
  intro i
  have hi := i.isLt
  rcases hm with hm | hm <;> omega

end

section

universe u
variable {k : Type u} [Field k]

 
def HasWeightsBetween {M : Type*} [AddCommGroup M] [Module k M]
    (ρ : Representation k (SL2 k) M) (lo hi : ℤ) : Prop :=
  ∀ (m : ℤ) (v : M), m < lo ∨ hi < m →
    (∀ a, ρ (diagonalTorus k a) v = integerCharacter k m a • v) → v = 0

lemma hasWeightsBetween_extension {L M N : Type*}
    [AddCommGroup L] [Module k L] [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N]
    (α : Representation k (SL2 k) L) (β : Representation k (SL2 k) M)
    (γ : Representation k (SL2 k) N) (f : L →ₗ[k] M) (g : M →ₗ[k] N)
    (hf : Function.Injective f) (he : LinearMap.ker g = LinearMap.range f)
    (hfi : ∀ x a, f (α a x) = β a (f x))
    (hgi : ∀ x a, g (β a x) = γ a (g x))
    (lo hi : ℤ) (hα : HasWeightsBetween α lo hi) (hγ : HasWeightsBetween γ lo hi) :
    HasWeightsBetween β lo hi := by
  intro m v hm hv
  have hgv : g v = 0 := hγ m (g v) hm (fun a => by
    rw [← hgi, hv, map_smul])
  have hvf : v ∈ LinearMap.range f := he ▸ hgv
  obtain ⟨v', hv'⟩ := hvf
  have hv'0 : v' = 0 := hα m v' hm (fun a => by
    apply hf
    rw [hfi, hv', hv, map_smul, hv'])
  simpa [hv'0] using hv'.symm

 
lemma highest_unipotent_fixed [Infinite k] {M : Type u} [AddCommGroup M]
    [Module k M] [Module.Finite k M] (ρ : Representation k (SL2 k) M)
    (hρ : IsRational k ρ) (n : ℤ) (v : M)
    (hv : ∀ a, ρ (diagonalTorus k a) v = integerCharacter k n a • v)
    (hn : ∀ (m : ℤ) (w : M), n < m →
      (∀ a, ρ (diagonalTorus k a) w = integerCharacter k m a • w) → w = 0) :
    ∀ t, ρ (unipotent k t) v = v := by
  classical
  obtain ⟨c, hc⟩ := rational_unipotent_expansion k ρ hρ v
  have hz (i : ℕ) (hi : i ≠ 0) : c i = 0 :=
    hn (n + 2 * i) (c i) (by omega) (unipotent_coefficient_weight k ρ v n hv c hc i)
  have hc0 : c = Finsupp.single 0 (c 0) := by
    ext i
    by_cases hi : i = 0
    · subst i; simp
    · simp [hi, hz i hi]
  have hc' (t : k) : ρ (unipotent k t) v = c 0 := by
    rw [hc t]
    conv_lhs => rw [hc0]
    rw [Finsupp.sum_single_index]
    · simp only [pow_zero, one_smul]
    · exact smul_zero _
  have hv0 : v = c 0 := by
    simpa [unipotent_zero] using hc' 0
  intro t
  exact (hc' t).trans hv0.symm

end

universe u
variable (k : Type u) [Field k]

 
def lowerUnipotent (t : k) : SL2 k :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩

@[simp] lemma lowerUnipotent_zero : lowerUnipotent k 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerUnipotent]

lemma lowerUnipotent_add (s t : k) :
    lowerUnipotent k (s + t) = lowerUnipotent k s * lowerUnipotent k t := by
  apply Subtype.ext
  change !![1, 0; s + t, 1] = !![1, 0; s, 1] * !![1, 0; t, 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

@[simp] lemma lowerUnipotent_inv (t : k) :
    (lowerUnipotent k t)⁻¹ = lowerUnipotent k (-t) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← lowerUnipotent_add]
  simp

lemma lowerUnipotent_coordinate_mem_powerAlgebra (i j : Fin 2) :
    (fun t : k => lowerUnipotent k t i j) ∈ powerAlgebra k := by
  fin_cases i <;> fin_cases j
  · exact (powerAlgebra k).one_mem
  · exact (powerAlgebra k).zero_mem
  · change (fun t : k => t) ∈ powerAlgebra k
    simpa only [pow_one] using power_mem_powerAlgebra k 1
  · exact (powerAlgebra k).one_mem

lemma polynomial_on_lowerUnipotent_mem_powerAlgebra
    (P : MvPolynomial (Fin 2 × Fin 2) k) :
    (fun t : k => MvPolynomial.eval (fun ij => lowerUnipotent k t ij.1 ij.2) P) ∈
      powerAlgebra k := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    simpa only [MvPolynomial.eval_C, Pi.algebraMap_def, Algebra.algebraMap_self,
      RingHom.id_apply] using (powerAlgebra k).algebraMap_mem c
  | add P Q hP hQ =>
    simpa only [MvPolynomial.eval_add, Pi.add_def] using (powerAlgebra k).add_mem hP hQ
  | mul_X P ij hP =>
    simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X, Pi.mul_def] using
      (powerAlgebra k).mul_mem hP (lowerUnipotent_coordinate_mem_powerAlgebra k ij.1 ij.2)

lemma rational_lowerUnipotent_expansion {M : Type u} [AddCommGroup M]
    [Module k M] [Module.Finite k M] (ρ : Representation k (SL2 k) M)
    (hρ : IsRational k ρ) (v : M) : ∃ c : ℕ →₀ M, ∀ t : k,
      ρ (lowerUnipotent k t) v = c.sum (fun n x => t ^ n • x) := by
  apply vector_expansion_of_scalar_span
  intro φ
  obtain ⟨P, hP⟩ := hρ v φ
  have heq : (fun t : k => φ (ρ (lowerUnipotent k t) v)) =
      (fun t : k => MvPolynomial.eval (fun ij => lowerUnipotent k t ij.1 ij.2) P) := by
    funext t
    exact hP (lowerUnipotent k t)
  rw [heq, ← powerAlgebra_toSubmodule]
  exact polynomial_on_lowerUnipotent_mem_powerAlgebra k P

lemma diagonal_lowerUnipotent (a : kˣ) (t : k) :
    diagonalTorus k a * lowerUnipotent k t =
      lowerUnipotent k ((↑a⁻¹ : k) ^ 2 * t) * diagonalTorus k a := by
  apply Subtype.ext
  change !![(a : k), 0; 0, (↑a⁻¹ : k)] * !![1, 0; t, 1] =
    !![1, 0; (↑a⁻¹ : k) ^ 2 * t, 1] * !![(a : k), 0; 0, (↑a⁻¹ : k)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, pow_two, mul_comm, mul_left_comm]

lemma lowerUnipotent_coefficient_weight [Infinite k] {M : Type u}
    [AddCommGroup M] [Module k M] (ρ : Representation k (SL2 k) M)
    (v : M) (n : ℤ) (hv : ∀ a, ρ (diagonalTorus k a) v = integerCharacter k n a • v)
    (c : ℕ →₀ M) (hc : ∀ t, ρ (lowerUnipotent k t) v = c.sum (fun i x => t ^ i • x)) :
    ∀ i a, ρ (diagonalTorus k a) (c i) = integerCharacter k (n - 2 * i) a • c i := by
  classical
  intro i a
  by_cases hi : i ∈ c.support
  · apply sub_eq_zero.mp
    apply function_sum_eq_zero (fun (j : ℕ) (t : k) => t ^ j)
      (linearIndependent_powerFunctions k) c.support
      (fun j => ρ (diagonalTorus k a) (c j) - integerCharacter k (n - 2 * j) a • c j)
      ?_ i hi
    intro t
    calc
      ∑ j ∈ c.support, t ^ j •
          (ρ (diagonalTorus k a) (c j) - integerCharacter k (n - 2 * j) a • c j) =
          ρ (diagonalTorus k a) (c.sum (fun j x => t ^ j • x)) -
            integerCharacter k n a • c.sum (fun j x => ((↑a⁻¹ : k) ^ 2 * t) ^ j • x) := by
        simp only [Finsupp.sum, map_sum, map_smul, smul_sub, Finset.sum_sub_distrib,
          Finset.smul_sum, smul_smul]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        simp [integerCharacter, zpow_sub, zpow_mul, mul_pow, ← pow_mul,
          mul_comm, mul_left_comm]
      _ = 0 := by
        rw [← hc, ← hc]
        apply sub_eq_zero.mpr
        have hh := congrArg (fun g => ρ g v) (diagonal_lowerUnipotent k a t)
        simpa only [map_mul, Module.End.mul_apply, hv, map_smul] using hh
  · rw [Finsupp.notMem_support_iff.mp hi, map_zero, smul_zero]

 

lemma lowerUnipotent_degree_bound [Infinite k] {M : Type u}
    [AddCommGroup M] [Module k M] (ρ : Representation k (SL2 k) M)
    (n : ℕ) (hbound : HasWeightsBetween ρ (-(n : ℤ)) n)
    (v : M) (hv : ∀ a, ρ (diagonalTorus k a) v = integerCharacter k n a • v)
    (c : ℕ →₀ M) (hc : ∀ t, ρ (lowerUnipotent k t) v = c.sum (fun i x => t ^ i • x)) :
    ∀ i, n < i → c i = 0 := by
  intro i hi
  exact hbound ((n : ℤ) - 2 * i) (c i) (Or.inl (by omega))
    (lowerUnipotent_coefficient_weight k ρ v n hv c hc i)

end FiberFunctorProof
end

end OAI
