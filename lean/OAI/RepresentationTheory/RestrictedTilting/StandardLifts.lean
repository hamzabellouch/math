import Mathlib
import OAI.RepresentationTheory.RestrictedTilting.WeightBounds

namespace OAI

/-! Highest coefficients, Bruhat intertwiners and standard module lifts. -/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace FiberFunctorProof

universe u
variable (k : Type u) [Field k]

 
noncomputable def standardRepresentation (n : ℕ) :
    Representation k (SL2 k)
      (Module.Dual k (MvPolynomial.homogeneousSubmodule (Fin 2) k n)) :=
  Representation.dual ((homogeneousRepresentation n).comp (dualMatrix k))

noncomputable def standardBasis (n : ℕ) := (binaryBasis k n).dualBasis

noncomputable def standardHighest (n : ℕ) := standardBasis k n (0 : Fin (n + 1))

lemma eval_linearChange {ι : Type*} [Fintype ι] (A : Matrix ι ι k)
    (z : ι → k) (f : MvPolynomial ι k) :
    MvPolynomial.eval z (linearChange A f) =
      MvPolynomial.eval (fun i => ∑ j, A j i * z j) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf =>
    simp only [map_mul, linearChange_X, MvPolynomial.eval_sum,
      MvPolynomial.eval_C, MvPolynomial.eval_X, hf]

lemma standardHighest_apply (n : ℕ)
    (f : MvPolynomial.homogeneousSubmodule (Fin 2) k n) :
    standardHighest k n f = MvPolynomial.eval ![1, 0] f.val := by
  have heq : standardHighest k n =
      (MvPolynomial.aeval (R := k) ![(1 : k), 0]).toLinearMap.comp
        (MvPolynomial.homogeneousSubmodule (Fin 2) k n).subtype := by
    apply (binaryBasis k n).ext
    intro i
    rw [show standardHighest k n = (binaryBasis k n).dualBasis 0 from rfl,
      Module.Basis.dualBasis_apply_self]
    change (if i = 0 then 1 else 0) =
      MvPolynomial.eval ![1, 0] (binaryBasis k n i).val
    rw [binaryBasis_apply]
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, one_mul]
    by_cases hi : i = 0
    · subst i; simp
    · have hi' : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      simp [hi, hi']
  change (standardHighest k n) f = _
  rw [heq]
  rfl

@[simp] lemma unipotent_inv (t : k) : (unipotent k t)⁻¹ = unipotent k (-t) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← unipotent_add]
  simp only [add_neg_cancel, unipotent_zero]

lemma dualMatrix_inv (g : SL2 k) : dualMatrix k g⁻¹ =
    (g : Matrix (Fin 2) (Fin 2) k).transpose := by
  change ((g⁻¹)⁻¹ : SL2 k).val.transpose = _
  rw [inv_inv]

lemma standardHighest_upper_fixed (n : ℕ) (t : k) :
    standardRepresentation k n (unipotent k t) (standardHighest k n) =
      standardHighest k n := by
  ext f
  change standardHighest k n ((homogeneousRepresentation n (dualMatrix k ((unipotent k t)⁻¹))) f) = _
  simp only [standardHighest_apply]
  change MvPolynomial.eval ![1,0]
    (linearChange (dualMatrix k ((unipotent k t)⁻¹)) f.val) = _
  rw [eval_linearChange, dualMatrix_inv]
  have hrow : (fun i => ∑ j, (unipotent k t).val.transpose j i * ![(1 : k), 0] j) =
      ![1, 0] := by
    funext i
    change (∑ j, (unipotent k t i j) * ![(1 : k), 0] j) = _
    fin_cases i <;> simp [unipotent, Fin.sum_univ_two]
  rw [hrow]

lemma standardHighest_lower_orbit (n : ℕ) (t : k) :
    standardRepresentation k n (lowerUnipotent k t) (standardHighest k n) =
      ∑ i : Fin (n + 1), t ^ (i : ℕ) • standardBasis k n i := by
  apply (binaryBasis k n).ext
  intro i
  change standardHighest k n ((homogeneousRepresentation n (dualMatrix k ((lowerUnipotent k t)⁻¹)))
    (binaryBasis k n i)) = _
  rw [standardHighest_apply]
  change MvPolynomial.eval ![1,0]
    (linearChange (dualMatrix k ((lowerUnipotent k t)⁻¹)) (binaryBasis k n i).val) = _
  rw [eval_linearChange]
  have hrow : (fun i => ∑ j, dualMatrix k ((lowerUnipotent k t)⁻¹) j i * ![(1 : k), 0] j) =
      ![1, t] := by
    rw [dualMatrix_inv]
    funext i
    change (∑ j, (lowerUnipotent k t i j) * ![(1 : k), 0] j) = _
    fin_cases i <;> simp [lowerUnipotent, Fin.sum_univ_two]
  rw [hrow, binaryBasis_apply]
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, one_mul,
    standardBasis, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.Basis.dualBasis_apply_self, smul_eq_mul]
  simp

lemma standardBasis_weight (n : ℕ) (i : Fin (n + 1)) (a : kˣ) :
    standardRepresentation k n (diagonalTorus k a) (standardBasis k n i) =
      integerCharacter k ((n : ℤ) - 2 * i) a • standardBasis k n i := by
  apply (binaryBasis k n).ext
  intro j
  change standardBasis k n i ((costandard k n).ρ ((diagonalTorus k a)⁻¹)
    (binaryBasis k n j)) = _
  rw [← map_inv, costandard_basis_weight]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, standardBasis,
    Module.Basis.dualBasis_apply_self]
  by_cases hji : j = i
  · subst j
    simp only [ite_true, mul_one]
    change ((a⁻¹ ^ (2 * (i : ℤ) - n) : kˣ) : k) =
      ((a ^ ((n : ℤ) - 2 * i) : kˣ) : k)
    congr 1
    rw [inv_zpow, ← zpow_neg]
    congr 1
    omega
  · simp [hji]

lemma standardHighest_weight (n : ℕ) (a : kˣ) :
    standardRepresentation k n (diagonalTorus k a) (standardHighest k n) =
      integerCharacter k n a • standardHighest k n := by
  simpa only [standardHighest, Fin.val_zero, Nat.cast_zero, mul_zero, sub_zero] using
    standardBasis_weight k n 0 a


lemma linearIndependent_powerFunctionsOn (S : Set k) (hS : S.Infinite) :
    LinearIndependent k (fun (n : ℕ) (x : S) => (x : k) ^ n) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s a ha i hi
  have hp : (∑ j ∈ s, Polynomial.monomial j (a j)) = (0 : Polynomial k) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hS.mono
    intro x hx
    change Polynomial.eval x _ = Polynomial.eval x _
    have he := congrFun ha ⟨x, hx⟩
    simpa only [Polynomial.eval_finsetSum, Polynomial.eval_monomial,
      Polynomial.eval_zero, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply,
      smul_eq_mul] using he
  have hc := congrArg (fun p : Polynomial k => p.coeff i) hp
  simpa [Polynomial.coeff_monomial, hi] using hc


 
lemma upper_lower_bruhat (s t : k) (q : kˣ) (hq : (q : k) = 1 + s * t) :
    unipotent k s * lowerUnipotent k t =
      lowerUnipotent k (t / q) * diagonalTorus k q * unipotent k (s / q) := by
  apply Subtype.ext
  change !![1, s; 0, 1] * !![1, 0; t, 1] =
    !![1, 0; t / q, 1] * !![(q : k), 0; 0, (↑q⁻¹ : k)] * !![1, s / q; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, div_eq_mul_inv]
  · exact hq.symm
  · field_simp
  · field_simp
    linear_combination hq

lemma lower_eq_transvection (t : k) :
    lowerUnipotent k t = Matrix.SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) t := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerUnipotent, Matrix.SpecialLinearGroup.transvection_coe]

lemma upper_eq_transvection (t : k) :
    unipotent k t = Matrix.SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) t := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotent, Matrix.SpecialLinearGroup.transvection_coe]

 
lemma intertwiner_of_root_groups {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N]
    (ρ : Representation k (SL2 k) M) (σ : Representation k (SL2 k) N)
    (f : M →ₗ[k] N)
    (hu : ∀ t v, f (ρ (unipotent k t) v) = σ (unipotent k t) (f v))
    (hl : ∀ t v, f (ρ (lowerUnipotent k t) v) = σ (lowerUnipotent k t) (f v)) :
    ∀ g v, f (ρ g v) = σ g (f v) := by
  apply Matrix.SL2.transvection_induction
  · intro i j hij t
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa only [← upper_eq_transvection] using hu t
    · simpa only [← lower_eq_transvection] using hl t
    · exact (hij rfl).elim
  · intro a b ha hb v
    simp only [map_mul, Module.End.mul_apply, ha, hb]


 

lemma standard_lower_orbit_ext {M : Type*} [AddCommGroup M] [Module k M]
    (n : ℕ) (S : Set k) (hS : S.Infinite)
    (f g : Module.Dual k (MvPolynomial.homogeneousSubmodule (Fin 2) k n) →ₗ[k] M)
    (h : ∀ t ∈ S, f (standardRepresentation k n (lowerUnipotent k t)
      (standardHighest k n)) = g (standardRepresentation k n (lowerUnipotent k t)
      (standardHighest k n))) : f = g := by
  classical
  apply (standardBasis k n).ext
  intro i
  apply sub_eq_zero.mp
  apply function_sum_eq_zero (fun (j : Fin (n+1)) (t : S) => (t : k) ^ (j : ℕ))
    ((linearIndependent_powerFunctionsOn k S hS).comp Fin.val Fin.val_injective)
    Finset.univ (fun j => f (standardBasis k n j) - g (standardBasis k n j)) ?_ i
    (Finset.mem_univ i)
  intro t
  have ht := h t t.property
  rw [standardHighest_lower_orbit] at ht
  simpa only [map_sum, map_smul, smul_sub, Finset.sum_sub_distrib, sub_eq_zero] using ht

lemma finsupp_sum_fin_of_degree_bound {M : Type*} [AddCommGroup M] [Module k M]
    (n : ℕ) (c : ℕ →₀ M) (hz : ∀ i, n < i → c i = 0) (t : k) :
    c.sum (fun i x => t ^ i • x) = ∑ i : Fin (n + 1), t ^ (i : ℕ) • c i := by
  classical
  have hs : c.support ⊆ Finset.range (n + 1) := by
    intro i hi
    apply Finset.mem_range.mpr
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hi) (hz i (by omega))
  rw [Finsupp.sum_of_support_subset c hs _ (fun i _ => smul_zero _)]
  exact (Fin.sum_univ_eq_sum_range (fun i => t ^ i • c i) (n + 1)).symm

 

noncomputable def highestCoefficientMap {M : Type*} [AddCommGroup M] [Module k M]
    (n : ℕ) (c : ℕ →₀ M) :
    Module.Dual k (MvPolynomial.homogeneousSubmodule (Fin 2) k n) →ₗ[k] M :=
  (standardBasis k n).constr k (fun i => c i)

lemma highestCoefficientMap_lower_orbit {M : Type*} [AddCommGroup M] [Module k M]
    (ρ : Representation k (SL2 k) M) (n : ℕ) (v : M) (c : ℕ →₀ M)
    (hc : ∀ t, ρ (lowerUnipotent k t) v = c.sum (fun i x => t ^ i • x))
    (hz : ∀ i, n < i → c i = 0) (t : k) :
    highestCoefficientMap k n c (standardRepresentation k n (lowerUnipotent k t)
      (standardHighest k n)) = ρ (lowerUnipotent k t) v := by
  rw [standardHighest_lower_orbit, hc, finsupp_sum_fin_of_degree_bound k n c hz]
  simp [highestCoefficientMap]

lemma highestCoefficientMap_highest {M : Type*} [AddCommGroup M] [Module k M]
    (ρ : Representation k (SL2 k) M) (n : ℕ) (v : M) (c : ℕ →₀ M)
    (hc : ∀ t, ρ (lowerUnipotent k t) v = c.sum (fun i x => t ^ i • x))
    (hz : ∀ i, n < i → c i = 0) :
    highestCoefficientMap k n c (standardHighest k n) = v := by
  simpa only [lowerUnipotent_zero, map_one, Module.End.one_apply] using
    highestCoefficientMap_lower_orbit k ρ n v c hc hz 0

lemma highestCoefficientMap_lower_intertwines [Infinite k]
    {M : Type*} [AddCommGroup M] [Module k M]
    (ρ : Representation k (SL2 k) M) (n : ℕ) (v : M) (c : ℕ →₀ M)
    (hc : ∀ t, ρ (lowerUnipotent k t) v = c.sum (fun i x => t ^ i • x))
    (hz : ∀ i, n < i → c i = 0) (s : k) :
    (highestCoefficientMap k n c).comp (standardRepresentation k n (lowerUnipotent k s)) =
      (ρ (lowerUnipotent k s)).comp (highestCoefficientMap k n c) := by
  apply standard_lower_orbit_ext k n Set.univ Set.infinite_univ
  intro t ht
  simp only [LinearMap.comp_apply]
  rw [← Module.End.mul_apply, ← map_mul, ← lowerUnipotent_add,
    highestCoefficientMap_lower_orbit k ρ n v c hc hz,
    highestCoefficientMap_lower_orbit k ρ n v c hc hz,
    lowerUnipotent_add, map_mul, Module.End.mul_apply]


lemma infinite_bruhat_parameters [Infinite k] (s : k) :
    {t : k | 1 + s * t ≠ 0}.Infinite := by
  by_cases hs : s = 0
  · simpa [hs] using (Set.infinite_univ (α := k))
  · have hf : {t : k | 1 + s * t = 0}.Finite := by
      apply (Set.finite_singleton (-s⁻¹)).subset
      intro t ht
      apply Set.mem_singleton_iff.mpr
      apply mul_left_cancel₀ hs
      rw [mul_neg, mul_inv_cancel₀ hs]
      change 1 + s * t = 0 at ht
      linear_combination ht
    exact hf.infinite_compl

lemma upper_lower_on_highest {M : Type*} [AddCommGroup M] [Module k M]
    (ρ : Representation k (SL2 k) M) (n : ℤ) (v : M)
    (hu : ∀ t, ρ (unipotent k t) v = v)
    (hv : ∀ a, ρ (diagonalTorus k a) v = integerCharacter k n a • v)
    (s t : k) (q : kˣ) (hq : (q : k) = 1 + s * t) :
    ρ (unipotent k s) (ρ (lowerUnipotent k t) v) =
      integerCharacter k n q • ρ (lowerUnipotent k (t / q)) v := by
  rw [← Module.End.mul_apply, ← map_mul, upper_lower_bruhat k s t q hq]
  simp only [map_mul, Module.End.mul_apply, hu, hv, map_smul]

lemma highestCoefficientMap_upper_intertwines [Infinite k]
    {M : Type*} [AddCommGroup M] [Module k M]
    (ρ : Representation k (SL2 k) M) (n : ℕ) (v : M)
    (hu : ∀ t, ρ (unipotent k t) v = v)
    (hv : ∀ a, ρ (diagonalTorus k a) v = integerCharacter k n a • v)
    (c : ℕ →₀ M)
    (hc : ∀ t, ρ (lowerUnipotent k t) v = c.sum (fun i x => t ^ i • x))
    (hz : ∀ i, n < i → c i = 0) (s : k) :
    (highestCoefficientMap k n c).comp (standardRepresentation k n (unipotent k s)) =
      (ρ (unipotent k s)).comp (highestCoefficientMap k n c) := by
  apply standard_lower_orbit_ext k n {t : k | 1 + s * t ≠ 0}
    (infinite_bruhat_parameters k s)
  intro t ht
  let q : kˣ := Units.mk0 (1 + s * t) ht
  simp only [LinearMap.comp_apply]
  rw [upper_lower_on_highest k (standardRepresentation k n) n (standardHighest k n)
    (standardHighest_upper_fixed k n) (standardHighest_weight k n) s t q rfl,
    map_smul, highestCoefficientMap_lower_orbit k ρ n v c hc hz,
    highestCoefficientMap_lower_orbit k ρ n v c hc hz,
    upper_lower_on_highest k ρ n v hu hv s t q rfl]

 

theorem exists_standard_lift [Infinite k] {M : Type u} [AddCommGroup M]
    [Module k M] [Module.Finite k M]
    (ρ : Representation k (SL2 k) M) (hρ : IsRational k ρ)
    (n : ℕ) (hbound : HasWeightsBetween ρ (-(n : ℤ)) n)
    (v : M) (hv : ∀ a, ρ (diagonalTorus k a) v = integerCharacter k n a • v) :
    ∃ f : Module.Dual k (MvPolynomial.homogeneousSubmodule (Fin 2) k n) →ₗ[k] M,
      f (standardHighest k n) = v ∧
      ∀ g x, f (standardRepresentation k n g x) = ρ g (f x) := by
  obtain ⟨c, hc⟩ := rational_lowerUnipotent_expansion k ρ hρ v
  have hz := lowerUnipotent_degree_bound k ρ n hbound v hv c hc
  have hu := highest_unipotent_fixed ρ hρ n v hv
    (fun m w hm hw => hbound m w (Or.inr hm) hw)
  refine ⟨highestCoefficientMap k n c,
    highestCoefficientMap_highest k ρ n v c hc hz, ?_⟩
  apply intertwiner_of_root_groups k
  · intro t x
    exact congrArg (fun f => (f : _ →ₗ[k] M) x)
      (highestCoefficientMap_upper_intertwines k ρ n v hu hv c hc hz t)
  · intro t x
    exact congrArg (fun f => (f : _ →ₗ[k] M) x)
      (highestCoefficientMap_lower_intertwines k ρ n v c hc hz t)

end FiberFunctorProof
end

end OAI
