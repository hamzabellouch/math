import OAI.RepresentationTheory.VertexAlgebra.ModuleEnergyModel

namespace OAI

noncomputable section
namespace StronglyRationalVOA.WeakModule
universe u v
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
  {W : Type v} [AddCommGroup W] [Module ℂ W]
  {A : VertexAlgebra V} (M : WeakModule A W)

theorem mode_commutator_nat (a b : V) (c : W) (m : ℕ) (k : ℤ) :
    mode M.fields a m (mode M.fields b k c) -
      mode M.fields b k (mode M.fields a m c) =
    ∑ j ∈ Finset.range (m + 1), (m.choose j : ℂ) •
      mode M.fields (mode A.fields a j b) ((m : ℤ) + k - j) c := by
  rw [M.mode_commutator]
  simp only [Int.cast_natCast, Ring.choose_natCast]
  apply finsum_eq_sum_of_support_subset
  intro j hj
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  have he : m.choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
  apply hj
  simp only [he, Nat.cast_zero, zero_smul]

 

theorem mode_iterate (a b : V) (c : W) (n k : ℤ) :
    mode M.fields (mode A.fields a n b) k c =
      ∑ᶠ j : ℕ, ((-1 : ℂ) ^ j * Ring.choose (n : ℂ) j) •
        (mode M.fields a (n - j) (mode M.fields b (k + j) c) -
          (-1 : ℂ) ^ n • mode M.fields b (n + k - j) (mode M.fields a j c)) := by
  have h := M.jacobi a b c 0 n k
  have hz (j : ℕ) (hj : j ≠ 0) : Ring.choose (0 : ℂ) j = 0 := by
    rw [← Nat.cast_zero, Ring.choose_natCast,
      Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj), Nat.cast_zero]
  conv_lhs at h =>
    rw [finsum_eq_single _ 0 (by
      intro j hj
      simp only [Int.cast_zero, hz j hj, zero_smul])]
  simpa only [Int.cast_zero, Ring.choose_zero_right, Nat.cast_zero, add_zero,
    sub_zero, zero_add, one_smul] using h

 

theorem mode_normal_product (a b : V) (c : W) (k : ℤ) :
    mode M.fields (mode A.fields a (-1) b) k c =
      ∑ᶠ j : ℕ,
        (mode M.fields a (-1 - j) (mode M.fields b (k + j) c) +
         mode M.fields b (k - 1 - j) (mode M.fields a j c)) := by
  have h := M.jacobi a b c 0 (-1) k
  have hz (j : ℕ) (hj : j ≠ 0) : Ring.choose (0 : ℂ) j = 0 := by
    rw [← Nat.cast_zero, Ring.choose_natCast,
      Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj), Nat.cast_zero]
  have hcoef (j : ℕ) : (-1 : ℂ)^j * Ring.choose (-1 : ℂ) j = 1 := by
    simp only [Ring.choose_neg', Ring.multichoose_one, Units.smul_def,
      Int.coe_negOnePow_natCast, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_one, mul_one, ← mul_pow]
    simp
  conv_lhs at h =>
    rw [finsum_eq_single _ 0 (by
      intro j hj
      simp only [Int.cast_zero, hz j hj, zero_smul])]
  have hn : (-1 : ℂ)^(-1 : ℤ) = -1 := by norm_num
  simpa only [Int.cast_zero, Int.cast_neg, Int.cast_one, Ring.choose_zero_right, Nat.cast_zero, add_zero,
    sub_zero, zero_add, one_smul, hcoef, hn, neg_one_smul, sub_neg_eq_add,
    show (-1 : ℤ) + k = k - 1 by omega] using h

 

theorem mode_normal_product_hasFiniteSupport (a b : V) (c : W) (k : ℤ) :
    (Function.support fun j : ℕ =>
        mode M.fields a (-1 - j) (mode M.fields b (k + j) c) +
        mode M.fields b (k - 1 - j) (mode M.fields a j c)).Finite := by
  have h₁ := mode_shift_hasFiniteSupport M.fields b c k
  have h₂ := mode_shift_hasFiniteSupport M.fields a c 0
  apply (h₁.union h₂).subset
  intro j hj
  by_contra h
  have he₁ : mode M.fields b (k + j) c = 0 := by
    by_contra hn
    exact h (Or.inl hn)
  have he₂ : mode M.fields a j c = 0 := by
    by_contra hn
    apply h
    right
    change mode M.fields a (0 + j) c ≠ 0
    simpa only [zero_add] using hn
  exact hj (by simp only [he₁, he₂, map_zero, add_zero])

 

theorem mode_normal_product_resplit (a b : V) (c : W) (k : ℤ) (t : ℕ) :
    mode M.fields (mode A.fields a (-1) b) k c =
      (∑ᶠ j : ℕ, mode M.fields a ((t : ℤ) - 1 - j)
        (mode M.fields b (k - t + j) c)) +
      (∑ᶠ j : ℕ, mode M.fields b (k - 1 - t - j)
        (mode M.fields a ((t : ℤ) + j) c)) -
      ∑ i ∈ Finset.range t,
        (mode M.fields a i (mode M.fields b (k - 1 - i) c) -
          mode M.fields b (k - 1 - i) (mode M.fields a i c)) := by
  classical
  have hleft (s : ℤ) : Function.HasFiniteSupport (fun j : ℕ =>
      mode M.fields a (s - 1 - j) (mode M.fields b (k - s + j) c)) := by
    apply (mode_shift_hasFiniteSupport M.fields b c (k - s)).subset
    intro j hj
    change _ ≠ 0 at hj ⊢
    intro hz
    exact hj (by dsimp at hz ⊢; rw [hz, map_zero])
  have hright (s : ℤ) : Function.HasFiniteSupport (fun j : ℕ =>
      mode M.fields b (k - 1 - s - j) (mode M.fields a (s + j) c)) := by
    apply (mode_shift_hasFiniteSupport M.fields a c s).subset
    intro j hj
    change _ ≠ 0 at hj ⊢
    intro hz
    exact hj (by dsimp at hz ⊢; rw [hz, map_zero])
  have hL := finsum_nat_split
    (fun j : ℕ => mode M.fields a ((t : ℤ) - 1 - j)
      (mode M.fields b (k - t + j) c)) (hleft t) t
  have hR := finsum_nat_split
    (fun j : ℕ => mode M.fields b (k - 1 - j) (mode M.fields a j c))
    (by simpa only [sub_zero, zero_add] using hright 0) t
  have htail : (∑ᶠ j : ℕ, mode M.fields a ((t : ℤ) - 1 - (t + j : ℕ))
      (mode M.fields b (k - t + (t + j : ℕ)) c)) =
      ∑ᶠ j : ℕ, mode M.fields a (-1 - j) (mode M.fields b (k + j) c) := by
    apply finsum_congr
    intro j
    simp only [Nat.cast_add]
    rw [show (t : ℤ) - 1 - (t + j) = -1 - j by omega,
      show k - (t : ℤ) + (t + j) = k + j by omega]
  have htailR : (∑ᶠ j : ℕ, mode M.fields b (k - 1 - (t + j : ℕ))
      (mode M.fields a (t + j : ℕ) c)) =
      ∑ᶠ j : ℕ, mode M.fields b (k - 1 - t - j)
        (mode M.fields a ((t : ℤ) + j) c) := by
    apply finsum_congr
    intro j
    simp only [Nat.cast_add]
    rw [show k - 1 - ((t : ℤ) + j) = k - 1 - t - j by omega]
  have hhead : (∑ j ∈ Finset.range t,
      mode M.fields a ((t : ℤ) - 1 - j) (mode M.fields b (k - t + j) c)) =
      ∑ j ∈ Finset.range t, mode M.fields a j (mode M.fields b (k - 1 - j) c) := by
    rw [← Finset.sum_range_reflect
      (fun j : ℕ => mode M.fields a j (mode M.fields b (k - 1 - j) c)) t]
    apply Finset.sum_congr rfl
    intro j hj
    have hcast : ((t - 1 - j : ℕ) : ℤ) = (t : ℤ) - 1 - j := by
      simp only [Finset.mem_range] at hj
      omega
    rw [hcast, show k - 1 - ((t : ℤ) - 1 - j) = k - t + j by omega]
  rw [htail, hhead] at hL
  rw [htailR] at hR
  rw [M.mode_normal_product, finsum_add_distrib
    (by simpa only [zero_sub, sub_zero] using hleft 0)
    (by simpa only [sub_zero, zero_add] using hright 0), Finset.sum_sub_distrib]
  rw [hL, hR]
  abel

 
theorem translation_covariance (a : V) (k : ℤ) :
    mode M.fields (A.translation a) k = -(k : ℂ) • mode M.fields a (k-1) := by
  ext x
  change mode M.fields (mode A.fields a (-2) A.vacuum) k x = _
  rw [M.mode_iterate]
  have hcoef (j : ℕ) : (-1 : ℂ)^j * Ring.choose (-2 : ℂ) j = (j : ℂ)+1 := by
    rw [show (-2 : ℂ)=-(2 : ℂ) by ring, Ring.choose_neg', Ring.multichoose_two]
    simp only [Units.smul_def, Int.coe_negOnePow_natCast, zsmul_eq_mul,
      Int.cast_pow, Int.cast_neg, Int.cast_one]
    calc
      _ = ((-1 : ℂ)*(-1))^j*((j : ℂ)+1) := by rw [mul_pow]; ring
      _ = _ := by norm_num
  have hn : (-1 : ℂ)^(-2 : ℤ)=1 := by norm_num
  simp only [Int.cast_neg, Int.cast_ofNat, hcoef, hn, one_smul]
  by_cases hk : k < 0
  · let j : ℕ := (-k-1).toNat
    have hj : (j : ℤ) = -k-1 := Int.toNat_of_nonneg (by omega)
    rw [finsum_eq_single _ j (by
      intro i hi
      have h1 : k+(i : ℤ) ≠ -1 := by intro he; apply hi; omega
      have h2 : -2+k-(i : ℤ) ≠ -1 := by omega
      rw [M.vacuum_mode, ite_eq_right h1, M.vacuum_mode, ite_eq_right h2]
      simp)]
    rw [M.vacuum_mode, ite_eq_left (by omega), M.vacuum_mode, ite_eq_right (by omega)]
    simp only [Module.End.one_apply, LinearMap.zero_apply, sub_zero,
      LinearMap.smul_apply]
    rw [show -2-(j : ℤ)=k-1 by omega]
    congr 1
    have hjc : (j : ℂ)=-(k : ℂ)-1 := by exact_mod_cast hj
    rw [hjc]; ring
  · by_cases hk0 : k=0
    · subst k
      rw [finsum_eq_zero_of_forall_eq_zero (by
        intro i
        rw [M.vacuum_mode, ite_eq_right (by omega), M.vacuum_mode, ite_eq_right (by omega)]
        simp)]
      simp
    · let j : ℕ := (k-1).toNat
      have hj : (j : ℤ) = k-1 := Int.toNat_of_nonneg (by omega)
      rw [finsum_eq_single _ j (by
        intro i hi
        have h1 : k+(i : ℤ) ≠ -1 := by omega
        have h2 : -2+k-(i : ℤ) ≠ -1 := by intro he; apply hi; omega
        rw [M.vacuum_mode, ite_eq_right h1, M.vacuum_mode, ite_eq_right h2]
        simp)]
      rw [M.vacuum_mode, ite_eq_right (by omega), M.vacuum_mode, ite_eq_left (by omega)]
      simp only [LinearMap.zero_apply, map_zero, Module.End.one_apply, zero_sub,
        smul_neg, LinearMap.smul_apply]
      rw [hj, ← neg_smul]
      congr 1
      have hjc : (j : ℂ)=(k : ℂ)-1 := by exact_mod_cast hj
      rw [hjc]; ring
end StronglyRationalVOA.WeakModule

end

end OAI
