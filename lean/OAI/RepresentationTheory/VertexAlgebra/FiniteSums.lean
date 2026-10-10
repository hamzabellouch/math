import Mathlib

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section



 

namespace StronglyRationalVOA

universe u v

 

theorem finite_sum_power_contraction {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (P : ℕ) (hP : 1 ≤ P) (R : ℝ) (hR : 1 ≤ R)
    (hx : ∀ i ∈ s, 0 ≤ x i)
    (H : ∀ i ∈ s, (x i)^P ≤ R * (1 + ∑ j ∈ s, x j)^(P - 1)) :
    1 + ∑ i ∈ s, x i ≤ ((s.card : ℝ) + 1)^P * R := by
  classical
  let B : ℝ := 1 + ∑ i ∈ s, x i
  have hB : 1 ≤ B := by
    dsimp [B]
    linarith [Finset.sum_nonneg hx]
  have hRhs : 1 ≤ R * B^(P - 1) := by
    nlinarith [one_le_pow₀ hB (n := P - 1)]
  have hmax : ∃ M : ℝ, 1 ≤ M ∧ (∀ i ∈ s, x i ≤ M) ∧ M^P ≤ R * B^(P - 1) := by
    by_cases hs : s.Nonempty
    · obtain ⟨i, hi, hmax⟩ := s.exists_max_image x hs
      refine ⟨max 1 (x i), le_max_left _ _, ?_, ?_⟩
      · intro j hj
        exact (hmax j hj).trans (le_max_right _ _)
      · rcases le_total (x i) 1 with h | h
        · rw [max_eq_left h, one_pow]
          exact hRhs
        · rw [max_eq_right h]
          exact H i hi
    · refine ⟨1, le_rfl, ?_, ?_⟩
      · intro i hi
        exact (hs ⟨i, hi⟩).elim
      · simpa only [one_pow] using hRhs
  obtain ⟨M, hM, hmax, hMP⟩ := hmax
  have hBM : B ≤ ((s.card : ℝ) + 1) * M := by
    have hsum : ∑ i ∈ s, x i ≤ (s.card : ℝ) * M := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using
        Finset.sum_le_sum (fun i hi => hmax i hi)
    dsimp [B]
    nlinarith
  have hp : B^P ≤ (((s.card : ℝ) + 1)^P * R) * B^(P - 1) := by
    calc
      _ ≤ (((s.card : ℝ) + 1) * M)^P := pow_le_pow_left₀ (by linarith) hBM P
      _ = ((s.card : ℝ) + 1)^P * M^P := mul_pow _ _ _
      _ ≤ ((s.card : ℝ) + 1)^P * (R * B^(P - 1)) :=
        mul_le_mul_of_nonneg_left hMP (by positivity)
      _ = _ := by ring
  have he : P - 1 + 1 = P := by omega
  rw [← he, pow_succ] at hp
  have hpos : 0 < B^(P - 1) := pow_pos (by linarith) _
  change B ≤ _
  apply (mul_le_mul_iff_of_pos_right hpos).mp
  simpa only [he, mul_comm] using hp

 

theorem finite_weighted_poly_uniform {ι κ : Type*} {B : ℕ → ℝ}
    (hB : ∀ N, 1 ≤ B N) (s : Finset ι) (f : ι → ℕ → κ → ℝ)
    (w : ι → ℕ) (T : ℕ → κ → Prop)
    (H : ∀ i ∈ s, ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ N x, T N x →
      f i N x ≤ C * (1 + (N : ℝ))^p * B N ^ w i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ i ∈ s, ∀ N x, T N x →
      f i N x ≤ C * (1 + (N : ℝ))^p * B N ^ w i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, 0, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨C, hC, p, hp⟩ := H i (Finset.mem_insert_self _ _)
    obtain ⟨D, hD, q, hq⟩ := ih (fun j hj => H j (Finset.mem_insert_of_mem hj))
    refine ⟨C + D, add_nonneg hC hD, p + q, ?_⟩
    intro j hj N x hx
    have hBN : 0 ≤ B N := zero_le_one.trans (hB N)
    have hN1 : 1 ≤ 1 + (N : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg N)
    have hpq : (1 + (N : ℝ))^p ≤ (1 + (N : ℝ))^(p + q) :=
      pow_le_pow_right₀ hN1 (by omega)
    have hqp : (1 + (N : ℝ))^q ≤ (1 + (N : ℝ))^(p + q) :=
      pow_le_pow_right₀ hN1 (by omega)
    rcases Finset.mem_insert.mp hj with rfl | hj
    · apply (hp N x hx).trans
      gcongr
      exact le_add_of_nonneg_right hD
    · apply (hq j hj N x hx).trans
      gcongr
      exact le_add_of_nonneg_left hC

section FiniteSums

variable {E : Type*} [AddCommMonoid E]

 
theorem finsum_nat_split (f : ℕ → E) (hf : Function.HasFiniteSupport f) (n : ℕ) :
    (∑ᶠ j : ℕ, f j) = (∑ j ∈ Finset.range n, f j) + ∑ᶠ j : ℕ, f (n + j) := by
  classical
  let N := hf.toFinset.sup id + 1
  have hN : ∀ j, N ≤ j → f j = 0 := by
    intro j hj
    by_contra h
    have hjmem : j ∈ hf.toFinset := by exact (Set.Finite.mem_toFinset hf).mpr h
    have hh := Finset.le_sup (f := id) hjmem
    change j ≤ hf.toFinset.sup id at hh
    omega
  have hs : Function.support f ⊆ (Finset.range (n + N) : Set ℕ) := by
    intro j hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hj (hN j (by omega))
  have ht : Function.support (fun j => f (n + j)) ⊆ (Finset.range N : Set ℕ) := by
    intro j hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hj (hN (n + j) (by omega))
  rw [finsum_eq_sum_of_support_subset f hs,
    finsum_eq_sum_of_support_subset _ ht, Finset.sum_range_add]

end FiniteSums

section Algebraic

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

 

abbrev StateField (V : Type u) (W : Type v)
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] :=
  V →ₗ[ℂ] VertexOperator ℂ W

 
def mode {W : Type v} [AddCommGroup W] [Module ℂ W]
    (Y : StateField V W) (a : V) (n : ℤ) : Module.End ℂ W :=
  VertexOperator.ncoeff (Y a) n

@[simp]
theorem mode_zero {W : Type v} [AddCommGroup W] [Module ℂ W]
    (Y : StateField V W) (n : ℤ) : mode Y 0 n = 0 := by
  simp [mode]

@[simp]
theorem mode_add {W : Type v} [AddCommGroup W] [Module ℂ W]
    (Y : StateField V W) (a b : V) (n : ℤ) :
    mode Y (a + b) n = mode Y a n + mode Y b n := by
  simp [mode]

@[simp]
theorem mode_smul {W : Type v} [AddCommGroup W] [Module ℂ W]
    (Y : StateField V W) (z : ℂ) (a : V) (n : ℤ) :
    mode Y (z • a) n = z • mode Y a n := by
  simp [mode]

 

theorem mode_lower_truncation {W : Type v} [AddCommGroup W] [Module ℂ W]
    (Y : StateField V W) (a : V) (b : W) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode Y a n b = 0 := by
  let o := HahnSeries.order ((HahnModule.of ℂ).symm (Y a b))
  refine ⟨-o, fun n hn => ?_⟩
  apply VertexOperator.ncoeff_eq_zero_of_lt_order
  change -n - 1 < o
  omega

 
theorem mode_shift_hasFiniteSupport {W : Type v} [AddCommGroup W] [Module ℂ W]
    (Y : StateField V W) (a : V) (b : W) (n : ℤ) :
    (Function.support fun j : ℕ => mode Y a (n + j) b).Finite := by
  obtain ⟨N, hN⟩ := mode_lower_truncation Y a b
  refine (Set.finite_Iio (N - n).toNat).subset ?_
  intro j hj
  have hn : n + (j : ℤ) < N := by
    by_contra h
    exact hj (hN (n + j) (by omega))
  change j < (N - n).toNat
  omega

 

def JacobiIdentity (Y : StateField V V) : Prop :=
  ∀ (a b c : V) (m n k : ℤ),
    (∑ᶠ j : ℕ, Ring.choose (m : ℂ) j •
      mode Y (mode Y a (n + j) b) (m + k - j) c) =
    ∑ᶠ j : ℕ, ((-1 : ℂ) ^ j * Ring.choose (n : ℂ) j) •
      (mode Y a (m + n - j) (mode Y b (k + j) c) -
        (-1 : ℂ) ^ n • mode Y b (n + k - j) (mode Y a (m + j) c))

 
structure VertexAlgebra (V : Type u) [AddCommGroup V] [Module ℂ V] where
  vacuum : V
  fields : StateField V V
  vacuum_mode : ∀ (n : ℤ), mode fields vacuum n = if n = -1 then 1 else 0
  creation : ∀ a : V, mode fields a (-1) vacuum = a
  creation_truncation : ∀ (a : V) (n : ℤ), 0 ≤ n → mode fields a n vacuum = 0
  jacobi : JacobiIdentity fields

namespace VertexAlgebra

variable (A : VertexAlgebra V)

 

theorem mode_commutator (a b c : V) (m k : ℤ) :
    mode A.fields a m (mode A.fields b k c) -
      mode A.fields b k (mode A.fields a m c) =
    ∑ᶠ j : ℕ, Ring.choose (m : ℂ) j •
      mode A.fields (mode A.fields a j b) (m + k - j) c := by
  have h := A.jacobi a b c m 0 k
  have hz (j : ℕ) (hj : j ≠ 0) : Ring.choose (0 : ℂ) j = 0 := by
    rw [← Nat.cast_zero, Ring.choose_natCast,
      Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj), Nat.cast_zero]
  conv_rhs at h =>
    rw [finsum_eq_single _ 0 (by
      intro j hj
      simp only [Int.cast_zero, hz j hj, mul_zero, zero_smul])]
  simpa using h.symm

 

theorem mode_commutator_nat (a b c : V) (m : ℕ) (k : ℤ) :
    mode A.fields a m (mode A.fields b k c) -
      mode A.fields b k (mode A.fields a m c) =
    ∑ j ∈ Finset.range (m + 1), (m.choose j : ℂ) •
      mode A.fields (mode A.fields a j b) ((m : ℤ) + k - j) c := by
  rw [A.mode_commutator]
  simp only [Int.cast_natCast, Ring.choose_natCast]
  apply finsum_eq_sum_of_support_subset
  intro j hj
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  have he : m.choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
  apply hj
  simp only [he, Nat.cast_zero, zero_smul]

 

theorem mode_iterate (a b c : V) (n k : ℤ) :
    mode A.fields (mode A.fields a n b) k c =
      ∑ᶠ j : ℕ, ((-1 : ℂ) ^ j * Ring.choose (n : ℂ) j) •
        (mode A.fields a (n - j) (mode A.fields b (k + j) c) -
          (-1 : ℂ) ^ n • mode A.fields b (n + k - j) (mode A.fields a j c)) := by
  have h := A.jacobi a b c 0 n k
  have hz (j : ℕ) (hj : j ≠ 0) : Ring.choose (0 : ℂ) j = 0 := by
    rw [← Nat.cast_zero, Ring.choose_natCast,
      Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj), Nat.cast_zero]
  conv_lhs at h =>
    rw [finsum_eq_single _ 0 (by
      intro j hj
      simp only [Int.cast_zero, hz j hj, zero_smul])]
  simpa only [Int.cast_zero, Ring.choose_zero_right, Nat.cast_zero, add_zero,
    sub_zero, zero_add, one_smul] using h

 

theorem mode_normal_product (a b c : V) (k : ℤ) :
    mode A.fields (mode A.fields a (-1) b) k c =
      ∑ᶠ j : ℕ,
        (mode A.fields a (-1 - j) (mode A.fields b (k + j) c) +
         mode A.fields b (k - 1 - j) (mode A.fields a j c)) := by
  have h := A.jacobi a b c 0 (-1) k
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

 

theorem mode_normal_product_hasFiniteSupport (a b c : V) (k : ℤ) :
    (Function.support fun j : ℕ =>
        mode A.fields a (-1 - j) (mode A.fields b (k + j) c) +
        mode A.fields b (k - 1 - j) (mode A.fields a j c)).Finite := by
  have h₁ := mode_shift_hasFiniteSupport A.fields b c k
  have h₂ := mode_shift_hasFiniteSupport A.fields a c 0
  apply (h₁.union h₂).subset
  intro j hj
  by_contra h
  have he₁ : mode A.fields b (k + j) c = 0 := by
    by_contra hn
    exact h (Or.inl hn)
  have he₂ : mode A.fields a j c = 0 := by
    by_contra hn
    apply h
    right
    change mode A.fields a (0 + j) c ≠ 0
    simpa only [zero_add] using hn
  exact hj (by simp only [he₁, he₂, map_zero, add_zero])

 

theorem mode_normal_product_resplit (a b c : V) (k : ℤ) (t : ℕ) :
    mode A.fields (mode A.fields a (-1) b) k c =
      (∑ᶠ j : ℕ, mode A.fields a ((t : ℤ) - 1 - j)
        (mode A.fields b (k - t + j) c)) +
      (∑ᶠ j : ℕ, mode A.fields b (k - 1 - t - j)
        (mode A.fields a ((t : ℤ) + j) c)) -
      ∑ i ∈ Finset.range t,
        (mode A.fields a i (mode A.fields b (k - 1 - i) c) -
          mode A.fields b (k - 1 - i) (mode A.fields a i c)) := by
  classical
  have hleft (s : ℤ) : Function.HasFiniteSupport (fun j : ℕ =>
      mode A.fields a (s - 1 - j) (mode A.fields b (k - s + j) c)) := by
    apply (mode_shift_hasFiniteSupport A.fields b c (k - s)).subset
    intro j hj
    change _ ≠ 0 at hj ⊢
    intro hz
    exact hj (by dsimp at hz ⊢; rw [hz, map_zero])
  have hright (s : ℤ) : Function.HasFiniteSupport (fun j : ℕ =>
      mode A.fields b (k - 1 - s - j) (mode A.fields a (s + j) c)) := by
    apply (mode_shift_hasFiniteSupport A.fields a c s).subset
    intro j hj
    change _ ≠ 0 at hj ⊢
    intro hz
    exact hj (by dsimp at hz ⊢; rw [hz, map_zero])
  have hL := finsum_nat_split
    (fun j : ℕ => mode A.fields a ((t : ℤ) - 1 - j)
      (mode A.fields b (k - t + j) c)) (hleft t) t
  have hR := finsum_nat_split
    (fun j : ℕ => mode A.fields b (k - 1 - j) (mode A.fields a j c))
    (by simpa only [sub_zero, zero_add] using hright 0) t
  have htail : (∑ᶠ j : ℕ, mode A.fields a ((t : ℤ) - 1 - (t + j : ℕ))
      (mode A.fields b (k - t + (t + j : ℕ)) c)) =
      ∑ᶠ j : ℕ, mode A.fields a (-1 - j) (mode A.fields b (k + j) c) := by
    apply finsum_congr
    intro j
    simp only [Nat.cast_add]
    rw [show (t : ℤ) - 1 - (t + j) = -1 - j by omega,
      show k - (t : ℤ) + (t + j) = k + j by omega]
  have htailR : (∑ᶠ j : ℕ, mode A.fields b (k - 1 - (t + j : ℕ))
      (mode A.fields a (t + j : ℕ) c)) =
      ∑ᶠ j : ℕ, mode A.fields b (k - 1 - t - j)
        (mode A.fields a ((t : ℤ) + j) c) := by
    apply finsum_congr
    intro j
    simp only [Nat.cast_add]
    rw [show k - 1 - ((t : ℤ) + j) = k - 1 - t - j by omega]
  have hhead : (∑ j ∈ Finset.range t,
      mode A.fields a ((t : ℤ) - 1 - j) (mode A.fields b (k - t + j) c)) =
      ∑ j ∈ Finset.range t, mode A.fields a j (mode A.fields b (k - 1 - j) c) := by
    rw [← Finset.sum_range_reflect
      (fun j : ℕ => mode A.fields a j (mode A.fields b (k - 1 - j) c)) t]
    apply Finset.sum_congr rfl
    intro j hj
    have hcast : ((t - 1 - j : ℕ) : ℤ) = (t : ℤ) - 1 - j := by
      simp only [Finset.mem_range] at hj
      omega
    rw [hcast, show k - 1 - ((t : ℤ) - 1 - j) = k - t + j by omega]
  rw [htail, hhead] at hL
  rw [htailR] at hR
  rw [A.mode_normal_product, finsum_add_distrib
    (by simpa only [zero_sub, sub_zero] using hleft 0)
    (by simpa only [sub_zero, zero_add] using hright 0), Finset.sum_sub_distrib]
  rw [hL, hR]
  abel

 

inductive ModeWord (S : ℕ → Set V) : ℕ → V → Prop
  | vacuum : ModeWord S 0 A.vacuum
  | cons {d t : ℕ} {a b : V} (ha : a ∈ S d) (hb : ModeWord S t b) (n : ℤ) :
      ModeWord S (d + t) (mode A.fields a n b)

 
def generatorFiltration (S : ℕ → Set V) (t : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {b | ∃ k ≤ t, A.ModeWord S k b}

theorem generatorFiltration_mono (S : ℕ → Set V) : Monotone (A.generatorFiltration S) := by
  intro s t hst
  apply Submodule.span_mono
  rintro b ⟨k, hk, hb⟩
  exact ⟨k, hk.trans hst, hb⟩

theorem modeWord_mem_generatorFiltration {S : ℕ → Set V} {t : ℕ} {b : V}
    (hb : A.ModeWord S t b) : b ∈ A.generatorFiltration S t :=
  Submodule.subset_span ⟨t, le_rfl, hb⟩

theorem vacuum_mem_generatorFiltration (S : ℕ → Set V) (t : ℕ) :
    A.vacuum ∈ A.generatorFiltration S t :=
  Submodule.subset_span ⟨0, Nat.zero_le _, ModeWord.vacuum⟩

 

theorem generator_mode_mem {S : ℕ → Set V} {d t : ℕ} {a b : V}
    (ha : a ∈ S d) (hb : b ∈ A.generatorFiltration S t) (n : ℤ) :
    mode A.fields a n b ∈ A.generatorFiltration S (d + t) := by
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨k, hk, hb⟩ := hb
    exact Submodule.subset_span ⟨d + k, Nat.add_le_add_left hk d, ModeWord.cons ha hb n⟩
  | zero => simp
  | add b c _ _ hb hc => simpa only [map_add] using Submodule.add_mem _ hb hc
  | smul z b _ hb => simpa only [map_smul] using Submodule.smul_mem _ z hb

 

theorem modeWord_mode_mem {S : ℕ → Set V} {t : ℕ} {a : V}
    (ha : A.ModeWord S t a) (s : ℕ) {b : V}
    (hb : b ∈ A.generatorFiltration S s) (n : ℤ) :
    mode A.fields a n b ∈ A.generatorFiltration S (t + s) := by
  induction ha generalizing s b n with
  | vacuum =>
    rw [A.vacuum_mode]
    split_ifs
    · simpa only [Module.End.one_apply, Nat.zero_add] using hb
    · simp
  | @cons d t a x ha hx k ih =>
    rw [A.mode_iterate]
    apply finsum_induction (fun x => x ∈ A.generatorFiltration S (d + t + s))
      (Submodule.zero_mem _) (fun _ _ => Submodule.add_mem _)
    intro j
    apply Submodule.smul_mem
    apply Submodule.sub_mem
    · simpa only [Nat.add_assoc] using A.generator_mode_mem ha (ih s hb (n + j)) (k - j)
    · apply Submodule.smul_mem
      have h := ih (d + s) (A.generator_mode_mem ha hb j) (k + n - j)
      simpa only [Nat.add_assoc, Nat.add_left_comm t d] using h

 

theorem generatorFiltration_mode_mem {S : ℕ → Set V} {t s : ℕ} {a b : V}
    (ha : a ∈ A.generatorFiltration S t) (hb : b ∈ A.generatorFiltration S s) (n : ℤ) :
    mode A.fields a n b ∈ A.generatorFiltration S (t + s) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨k, hk, ha⟩ := ha
    exact A.generatorFiltration_mono S (Nat.add_le_add_right hk s)
      (A.modeWord_mode_mem ha s hb n)
  | zero => simp
  | add a c _ _ ha hc =>
    simpa only [mode_add, LinearMap.add_apply] using Submodule.add_mem _ ha hc
  | smul z a _ ha =>
    simpa only [mode_smul, LinearMap.smul_apply] using Submodule.smul_mem _ z ha

 

inductive NegativeWord (S : ℕ → Set V) : ℕ → ℕ → V → Prop
  | vacuum : NegativeWord S 0 0 A.vacuum
  | cons {d t w : ℕ} {a b : V} (ha : a ∈ S d) (hb : NegativeWord S t w b) (n : ℕ) :
      NegativeWord S (d + t) (d + w + n) (mode A.fields a (-1 - n) b)

 
def negativeFiltration (S : ℕ → Set V) (t : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {b | ∃ k ≤ t, ∃ w, A.NegativeWord S k w b}

theorem negativeFiltration_mono (S : ℕ → Set V) : Monotone (A.negativeFiltration S) := by
  intro s t hst
  apply Submodule.span_mono
  rintro b ⟨k, hk, w, hb⟩
  exact ⟨k, hk.trans hst, w, hb⟩

theorem NegativeWord.modeWord {S : ℕ → Set V} {t w : ℕ} {a : V}
    (h : A.NegativeWord S t w a) : A.ModeWord S t a := by
  induction h with
  | vacuum => exact ModeWord.vacuum
  | cons ha _ n ih => exact ModeWord.cons ha ih (-1 - n)

theorem NegativeWord.weight_le {S : ℕ → Set V} {t w : ℕ} {a : V}
    (h : A.NegativeWord S t w a) : t ≤ w := by
  induction h with
  | vacuum => exact le_rfl
  | cons _ _ n ih => omega

theorem negativeWord_mem_negativeFiltration {S : ℕ → Set V} {t w : ℕ} {a : V}
    (ha : A.NegativeWord S t w a) : a ∈ A.negativeFiltration S t :=
  Submodule.subset_span ⟨t, le_rfl, w, ha⟩

theorem negativeFiltration_le (S : ℕ → Set V) (t : ℕ) :
    A.negativeFiltration S t ≤ A.generatorFiltration S t := by
  apply Submodule.span_le.mpr
  rintro a ⟨k, hk, w, ha⟩
  exact Submodule.subset_span ⟨k, hk, ha.modeWord⟩
end VertexAlgebra
end Algebraic
end StronglyRationalVOA

end

end OAI
