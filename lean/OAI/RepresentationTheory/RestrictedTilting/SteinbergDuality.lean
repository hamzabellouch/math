import Mathlib
import OAI.RepresentationTheory.RestrictedTilting.ExtensionSplitting

namespace OAI

/-! Standard-costandard maps, binomial coefficients and Steinberg self-duality. -/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace FiberFunctorProof
section
open CategoryTheory CategoryTheory.MonoidalCategory
universe u
variable (k : Type u) [Field k]

noncomputable def costandardHighest (n : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 2) k n := binaryBasis k n (Fin.last n)

lemma costandardHighest_weight (n : ℕ) (a : kˣ) :
    (costandard k n).ρ (diagonalTorus k a) (costandardHighest k n) =
      integerCharacter k n a • costandardHighest k n := by
  have h := costandard_basis_weight k n (Fin.last n) a
  have hn : (2 * (n : ℤ) - n) = n := by ring
  simpa [costandardHighest, hn] using h

lemma costandardHighest_lower_orbit (n : ℕ) (t : k) :
    (costandard k n).ρ (lowerUnipotent k t) (costandardHighest k n) =
      ∑ i : Fin (n + 1), t ^ (i : ℕ) •
        (((-1 : k) ^ (i : ℕ) * (n.choose i : k)) • binaryBasis k n i.rev) := by
  apply Subtype.ext
  change linearChange (dualMatrix k (lowerUnipotent k t))
      (binaryBasis k n (Fin.last n)).val = _
  rw [binaryBasis_apply]
  simp only [Fin.val_last, Nat.sub_self, pow_zero, one_mul, map_pow]
  have he : linearChange (dualMatrix k (lowerUnipotent k t)) (MvPolynomial.X 1) =
      (-MvPolynomial.C t * MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) k) := by
    simp [linearChange_X, dualMatrix, lowerUnipotent,
      Matrix.transpose_apply, Fin.sum_univ_two]
  rw [he, add_pow]
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, binaryBasis_apply,
    MvPolynomial.smul_eq_C_mul, Fin.val_rev, Nat.succ_sub_succ_eq_sub]
  apply Finset.sum_congr rfl
  intro i _
  have hi : n - (n - (i : ℕ)) = i := by omega
  rw [hi]
  have hneg : (-MvPolynomial.C t : MvPolynomial (Fin 2) k) =
      MvPolynomial.C (-1 : k) * MvPolynomial.C t := by simp
  rw [hneg]
  simp only [mul_pow, map_mul, map_pow, map_neg, map_one, map_natCast]
  ring

variable [Infinite k]

 

theorem exists_standard_costandard_map (n : ℕ) :
    ∃ f : Module.Dual k (MvPolynomial.homogeneousSubmodule (Fin 2) k n) →ₗ[k]
        MvPolynomial.homogeneousSubmodule (Fin 2) k n,
      (∀ a x, f (standardRepresentation k n a x) = (costandard k n).ρ a (f x)) ∧
      ∀ i : Fin (n + 1), f (standardBasis k n i) =
        ((-1 : k) ^ (i : ℕ) * (n.choose i : k)) • binaryBasis k n i.rev := by
  obtain ⟨f,hfv,hf⟩ := exists_standard_lift k (costandard k n).ρ (costandard_rational k n)
    n (fun m v hm hv => costandard_weight_bound k n m hm v hv)
    (costandardHighest k n) (costandardHighest_weight k n)
  change Module.Dual k (MvPolynomial.homogeneousSubmodule (Fin 2) k n) →ₗ[k]
    MvPolynomial.homogeneousSubmodule (Fin 2) k n at f
  refine ⟨f,hf,?_⟩
  intro i
  apply sub_eq_zero.mp
  apply function_sum_eq_zero (fun (j : Fin (n+1)) (t : k) => t ^ (j : ℕ))
    ((linearIndependent_powerFunctions k).comp Fin.val Fin.val_injective) Finset.univ
    (fun j => f (standardBasis k n j) -
      ((-1 : k) ^ (j : ℕ) * (n.choose j : k)) • binaryBasis k n j.rev) ?_ i
    (Finset.mem_univ i)
  intro t
  have ht := hf (lowerUnipotent k t) (standardHighest k n)
  rw [hfv, costandardHighest_lower_orbit, standardHighest_lower_orbit] at ht
  change f (∑ j : Fin (n+1), t ^ (j : ℕ) • standardBasis k n j) =
    ∑ j : Fin (n+1), t ^ (j : ℕ) •
      (((-1 : k) ^ (j : ℕ) * (n.choose j : k)) • binaryBasis k n j.rev) at ht
  simpa only [Finset.mem_univ, forall_const, Finset.sum_const_zero, map_sum, map_smul,
    smul_sub, Finset.sum_sub_distrib, Finset.sum_ite_irrel, ite_true, sub_eq_zero] using ht

 
theorem costandard_self_dual_of_choose_ne_zero (n : ℕ)
    (hc : ∀ i : Fin (n + 1), (n.choose i : k) ≠ 0) :
    Nonempty ((costandard k n)ᘁ ≅ costandard k n) := by
  obtain ⟨f,hf,hfb⟩ := exists_standard_costandard_map k n
  have hsurj : Function.Surjective f := by
    apply LinearMap.range_eq_top.mp
    have hr : Submodule.span k (Set.range (binaryBasis k n)) ≤ LinearMap.range f := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      let c : k := (-1 : k) ^ (i.rev : ℕ) * (n.choose i.rev : k)
      have hc' : c ≠ 0 := mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (hc i.rev)
      refine ⟨c⁻¹ • standardBasis k n i.rev, ?_⟩
      rw [map_smul, hfb, Fin.rev_rev]
      change c⁻¹ • (c • binaryBasis k n i) = _
      rw [inv_smul_smul₀ hc']
    rw [(binaryBasis k n).span_eq] at hr
    exact top_le_iff.mp hr
  have hinj : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := k))).mpr hsurj
  let f' : (costandard k n)ᘁ ⟶ costandard k n := fdrepHom k f (by
    intro a x
    rw [fdrep_dual_repr]
    exact hf a x)
  have : IsIso f' := fdrepHom_isIso_of_bijective k f' ⟨hinj,hsurj⟩
  exact ⟨asIso f'⟩

 

theorem costandard_tilting_of_choose_ne_zero (n : ℕ)
    (hc : ∀ i : Fin (n + 1), (n.choose i : k) ≠ 0) : IsTilting k (costandard k n) := by
  obtain ⟨e⟩ := costandard_self_dual_of_choose_ne_zero k n hc
  exact ⟨costandard_rational k n, costandard_hasGoodFiltration k n,
    (costandard_hasGoodFiltration k n).of_iso k e.symm⟩

end

section
universe u
variable (k : Type u) [Field k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]

lemma choose_cast_ne_zero_of_lt_char {n i : ℕ} (hn : n < p) (hi : i ≤ n) :
    (n.choose i : k) ≠ 0 := by
  have hp := (Fact.out : p.Prime)
  have hnf : (n.factorial : k) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff k p, hp.dvd_factorial]
    exact not_le.mpr hn
  intro h
  have he := congrArg (fun a : ℕ => (a : k)) (Nat.choose_mul_factorial_mul_factorial hi)
  simp only [Nat.cast_mul, h, zero_mul] at he
  exact hnf he.symm

lemma choose_prime_power_cast_eq_zero (m i : ℕ) (hi : 0 < i) (hi' : i < p ^ m) :
    ((p ^ m).choose i : k) = 0 := by
  have he : (Polynomial.X + 1 : Polynomial k) ^ p ^ m = Polynomial.X ^ p ^ m + 1 := by
    simpa using add_pow_char_pow (Polynomial.X : Polynomial k) 1 p m
  have h := congrArg (fun f : Polynomial k => f.coeff i) he
  simpa [Polynomial.coeff_X_add_one_pow, Polynomial.coeff_one, ne_of_gt hi, ne_of_lt hi'] using h

 

theorem choose_prime_power_sub_one_cast (m i : ℕ) (hi : i < p ^ m) :
    ((p ^ m - 1).choose i : k) = (-1 : k) ^ i := by
  have hq : 0 < p ^ m := pow_pos (Fact.out : p.Prime).pos m
  induction i with
  | zero => simp
  | succ i ih =>
    have hi' : i < p ^ m := by omega
    have hzero := choose_prime_power_cast_eq_zero k p m (i+1) (by omega) hi
    have hpasc := congrArg (fun a : ℕ => (a : k))
      (Nat.choose_succ_succ' (p ^ m - 1) i)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ p ^ m), Nat.cast_add] at hpasc
    rw [hzero, ih hi'] at hpasc
    rw [pow_succ]
    linear_combination -hpasc

lemma choose_prime_power_sub_one_ne_zero (m : ℕ) (i : Fin (p ^ m - 1 + 1)) :
    ((p ^ m - 1).choose i : k) ≠ 0 := by
  rw [choose_prime_power_sub_one_cast k p m i (by
    have hq : 0 < p ^ m := pow_pos (Fact.out : p.Prime).pos m
    have := i.isLt
    omega)]
  exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)

end

universe u
variable (k : Type u) [Field k] [Infinite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]

theorem small_costandard_tilting (n : ℕ) (hn : n < p) :
    IsTilting k (costandard k n) :=
  costandard_tilting_of_choose_ne_zero k n
    (fun i => choose_cast_ne_zero_of_lt_char k p hn (by omega))

 
theorem steinberg_tilting (m : ℕ) : IsTilting k (steinberg k p m) :=
  costandard_tilting_of_choose_ne_zero k (p ^ m - 1)
    (choose_prime_power_sub_one_ne_zero k p m)

theorem steinberg_self_dual (m : ℕ) :
    Nonempty ((steinberg k p m)ᘁ ≅ steinberg k p m) :=
  costandard_self_dual_of_choose_ne_zero k (p ^ m - 1)
    (choose_prime_power_sub_one_ne_zero k p m)

end FiberFunctorProof
end

end OAI
