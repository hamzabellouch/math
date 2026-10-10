import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.GradeComponentC

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
def BlockGrowth (B : ℕ → ℝ) (a : V) (d w : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ N,
    A.BlockControl a d N (C * (1 + (N : ℝ)) ^ p * B N ^ w)

theorem blockGrowth_zero (B : ℕ → ℝ) (d w : ℕ) : A.BlockGrowth B 0 d w := by
  refine ⟨0, le_rfl, 0, ?_⟩
  intro N
  simpa only [zero_mul] using A.blockControl_zero d N

theorem blockGrowth_add {B : ℕ → ℝ} (hB : ∀ N, 1 ≤ B N) {a b : V} {d w : ℕ}
    (ha : A.BlockGrowth B a d w) (hb : A.BlockGrowth B b d w) :
    A.BlockGrowth B (a + b) d w := by
  obtain ⟨C, hC, p, hp⟩ := ha
  obtain ⟨D, hD, q, hq⟩ := hb
  refine ⟨C + D, add_nonneg hC hD, p + q, fun N => ?_⟩
  apply A.blockControl_mono (A.blockControl_add (hp N) (hq N))
  have hBN : 0 ≤ B N := (zero_le_one.trans (hB N))
  have hNp : (1 + (N : ℝ)) ^ p ≤ (1 + (N : ℝ)) ^ (p + q) :=
    pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]) (by omega)
  have hNq : (1 + (N : ℝ)) ^ q ≤ (1 + (N : ℝ)) ^ (p + q) :=
    pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]) (by omega)
  calc
    _ ≤ C * (1 + (N : ℝ)) ^ (p + q) * B N ^ w +
        D * (1 + (N : ℝ)) ^ (p + q) * B N ^ w := by gcongr
    _ = _ := by ring

theorem blockGrowth_smul {B : ℕ → ℝ} {a : V} {d w : ℕ}
    (ha : A.BlockGrowth B a d w) (z : ℂ) : A.BlockGrowth B (z • a) d w := by
  obtain ⟨C, hC, p, hp⟩ := ha
  refine ⟨‖z‖ * C, mul_nonneg (norm_nonneg _) hC, p, fun N => ?_⟩
  simpa only [mul_assoc] using A.blockControl_smul (hp N) z

theorem blockGrowth_mono_weight {B : ℕ → ℝ} (hB : ∀ N, 1 ≤ B N)
    {a : V} {d w w' : ℕ} (ha : A.BlockGrowth B a d w) (hw : w ≤ w') :
    A.BlockGrowth B a d w' := by
  obtain ⟨C, hC, p, hp⟩ := ha
  refine ⟨C, hC, p, fun N => ?_⟩
  apply A.blockControl_mono (hp N)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hB N) hw) (by positivity)

 

theorem translation_blockGrowth {B : ℕ → ℝ} (hB : ∀ N, 1 ≤ B N)
    {a : V} {d w : ℕ} (ha : A.BlockGrowth B a d w) :
    A.BlockGrowth B (A.toVertexAlgebra.translation a) (d + 1) w := by
  obtain ⟨C, hC, p, hp⟩ := ha
  refine ⟨((d : ℝ) + 2) * C, by positivity, p + 1, ?_⟩
  intro N h hh k hk c hc
  have hBN : 0 ≤ B N := zero_le_one.trans (hB N)
  have he (m : ℤ) : A.physicalMode (A.toVertexAlgebra.translation a) (d + 1) m =
      (-(m + (d : ℤ) : ℤ) : ℂ) • A.physicalMode a d m := by
    simp only [physicalMode, Nat.cast_add, Nat.cast_one]
    rw [show m + ((d : ℤ) + 1) - 1 = m + d by omega, A.translation_covariance]
  rw [he, LinearMap.smul_apply, norm_smul]
  have hcoef : ‖(-((h : ℤ) - k + d) : ℤ)‖ ≤ ((d : ℝ) + 2) * (1 + (N : ℝ)) := by
    simp only [Int.norm_eq_abs, Int.cast_neg, Int.cast_add, Int.cast_sub, Int.cast_natCast, abs_neg]
    rw [abs_le]
    constructor <;> nlinarith [show (h : ℝ) ≤ N by exact_mod_cast hh,
      show (k : ℝ) ≤ N by exact_mod_cast hk, Nat.cast_nonneg (α := ℝ) h,
      Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) d,
      Nat.cast_nonneg (α := ℝ) N]
  have hcoef' : ‖(-(((h : ℤ) - k + d : ℤ) : ℂ))‖ ≤ ((d : ℝ) + 2) * (1 + (N : ℝ)) := by
    simpa only [norm_neg, Complex.norm_intCast, Int.norm_eq_abs, Int.cast_neg, abs_neg] using hcoef
  calc
    _ ≤ (((d : ℝ) + 2) * (1 + (N : ℝ))) *
        (C * (1 + (N : ℝ)) ^ p * B N ^ w * ‖c‖) := by
      exact mul_le_mul hcoef' (hp N h hh k hk c hc) (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_succ]; ring

 

theorem finite_blockGrowth_uniform {B : ℕ → ℝ} (hB : ∀ N, 1 ≤ B N)
    {ι : Type*} (s : Finset ι) (a : ι → V) (d w : ι → ℕ)
    (hg : ∀ i ∈ s, A.BlockGrowth B (a i) (d i) (w i)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ i ∈ s, ∀ N,
      A.BlockControl (a i) (d i) N (C * (1 + (N : ℝ)) ^ p * B N ^ w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, 0, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨C, hC, p, hp⟩ := hg i (Finset.mem_insert_self _ _)
    obtain ⟨D, hD, q, hq⟩ := ih (fun j hj => hg j (Finset.mem_insert_of_mem hj))
    refine ⟨C + D, add_nonneg hC hD, p + q, ?_⟩
    intro j hj N
    have hBN : 0 ≤ B N := zero_le_one.trans (hB N)
    have hNp : (1 + (N : ℝ)) ^ p ≤ (1 + (N : ℝ)) ^ (p + q) :=
      pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]) (by omega)
    have hNq : (1 + (N : ℝ)) ^ q ≤ (1 + (N : ℝ)) ^ (p + q) :=
      pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]) (by omega)
    rcases Finset.mem_insert.mp hj with rfl | hj
    · apply A.blockControl_mono (hp N)
      gcongr
      exact le_add_of_nonneg_right hD
    · apply A.blockControl_mono (hq j hj N)
      gcongr
      exact le_add_of_nonneg_left hC

 

theorem normalProduct_blockGrowth {B : ℕ → ℝ} (hB : ∀ N, 1 ≤ B N)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hd : 1 ≤ d)
    (Ha : A.BlockGrowth B a d d) (Hb : A.BlockGrowth B b e e)
    (Hsing : ∀ j < d - 1,
      A.BlockGrowth B (mode A.fields a j b) (d + e - j - 1) (d + e - j - 1)) :
    A.BlockGrowth B (mode A.fields a (-1) b) (d + e) (d + e) := by
  classical
  obtain ⟨C, hC, p, hp⟩ := Ha
  obtain ⟨D, hD, q, hq⟩ := Hb
  have hsG : ∀ j ∈ Finset.range (d - 1),
      A.BlockGrowth B (mode A.fields a j b) (d + e - j - 1) (d + e) := by
    intro j hj
    exact A.blockGrowth_mono_weight hB (Hsing j (Finset.mem_range.mp hj)) (by omega)
  obtain ⟨R, hR, s, hs⟩ := A.finite_blockGrowth_uniform hB (Finset.range (d - 1))
    (fun j => mode A.fields a j b) (fun j => d + e - j - 1) (fun _ => d + e) hsG
  refine ⟨2 * C * D + correctionMass d * R,
    add_nonneg (by positivity) (mul_nonneg (correctionMass_nonneg d) hR), p + q + s + 1, ?_⟩
  intro N
  have hBN : 0 ≤ B N := zero_le_one.trans (hB N)
  have hmass := correctionMass_nonneg d
  apply A.blockControl_mono (A.normalProduct_blockControl ha hb hd
    (by positivity) (by positivity) (hp N) (hq N)
    (fun j hj => hs j (Finset.mem_range.mpr hj) N))
  have hpow₁ : (1 + (N : ℝ)) ^ (p + q + 1) ≤ (1 + (N : ℝ)) ^ (p + q + s + 1) :=
    pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]) (by omega)
  have hpow₂ : (1 + (N : ℝ)) ^ s ≤ (1 + (N : ℝ)) ^ (p + q + s + 1) :=
    pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]) (by omega)
  calc
    _ = ((2 : ℝ) * N + 1) * (C * D * (1 + (N : ℝ)) ^ (p + q) * B N ^ (d + e)) +
        correctionMass d * R * (1 + (N : ℝ)) ^ s * B N ^ (d + e) := by
      simp only [pow_add]
      ring
    _ ≤ (2 * (1 + (N : ℝ))) * (C * D * (1 + (N : ℝ)) ^ (p + q) * B N ^ (d + e)) +
        correctionMass d * R * (1 + (N : ℝ)) ^ s * B N ^ (d + e) := by
      gcongr
      linarith
    _ = 2 * C * D * (1 + (N : ℝ)) ^ (p + q + 1) * B N ^ (d + e) +
        correctionMass d * R * (1 + (N : ℝ)) ^ s * B N ^ (d + e) := by
      rw [pow_succ]
      ring
    _ ≤ 2 * C * D * (1 + (N : ℝ)) ^ (p + q + s + 1) * B N ^ (d + e) +
        correctionMass d * R * (1 + (N : ℝ)) ^ (p + q + s + 1) * B N ^ (d + e) := by
      gcongr
    _ = _ := by ring

 

def blockGrowthSubmodule (B : ℕ → ℝ) (hB : ∀ N, 1 ≤ B N) (d w : ℕ) : Submodule ℂ V where
  carrier := {a | A.BlockGrowth B a d w}
  zero_mem' := A.blockGrowth_zero B d w
  add_mem' := A.blockGrowth_add hB
  smul_mem' z _ h := A.blockGrowth_smul h z

 
theorem vacuum_blockGrowth (B : ℕ → ℝ) : A.BlockGrowth B A.vacuum 0 0 := by
  refine ⟨1, zero_le_one, 0, fun N h hh k hk c hc => ?_⟩
  simp only [physicalMode, Nat.cast_zero, add_zero, A.vacuum_mode, pow_zero, mul_one, one_mul]
  split_ifs <;> simp

 

theorem homogeneousC2_le_blockGrowth {B : ℕ → ℝ} (hB : ∀ N, 1 ≤ B N) (w : ℕ)
    (hprev : ∀ d < w, ∀ a ∈ A.grade d, A.BlockGrowth B a d d) :
    A.homogeneousC2 w ≤ A.blockGrowthSubmodule B hB w w := by
  apply Submodule.span_le.mpr
  rintro x ⟨d, e, a, b, ha, hb, hweight, rfl⟩
  change A.BlockGrowth B (mode A.fields a (-2) b) w w
  by_cases he : e = 0
  · subst e
    have hweight' : w = d + 1 := by omega
    rw [A.grade_zero] at hb
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp hb
    rw [map_smul]
    have H := A.translation_blockGrowth hB (hprev d (by omega) a ha)
    have H' := A.blockGrowth_mono_weight hB H (show d ≤ w by omega)
    rw [hweight'] at H' ⊢
    exact A.blockGrowth_smul H' z
  · have hepos : 1 ≤ e := by omega
    have hTgrade : A.toVertexAlgebra.translation a ∈ A.grade (d + 1) := by
      rw [← A.virasoro_neg_one_eq_translation]
      exact A.virasoro_mem_grade ha (-1) (by omega)
    have hT := hprev (d + 1) (by omega) (A.toVertexAlgebra.translation a) hTgrade
    have hB' := hprev e (by omega) b hb
    have hsing : ∀ j < (d + 1) - 1,
        A.BlockGrowth B (mode A.fields (A.toVertexAlgebra.translation a) j b)
          (d + 1 + e - j - 1) (d + 1 + e - j - 1) := by
      intro j hj
      apply hprev _ (by omega)
      exact A.mode_mem_grade hTgrade hb j (by omega)
    have H := A.normalProduct_blockGrowth hB hTgrade hb (by omega) hT hB' hsing
    have heq : mode A.fields (A.toVertexAlgebra.translation a) (-1) b =
        mode A.fields a (-2) b := by
      rw [A.translation_covariance]
      norm_num
    rw [heq, show d + 1 + e = w by omega] at H
    exact H

 

theorem zeroMode_commutator {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (c : V) :
    A.virasoroMode 1 (A.physicalMode a d (-1) c) -
      A.physicalMode a d (-1) (A.virasoroMode 1 c) =
        (d : ℂ) • A.physicalMode a d 0 c := by
  have h := A.mode_commutator_nat A.conformalVector a c 2 ((d : ℤ) - 2)
  have hν0 : mode A.fields A.conformalVector 0 a = A.toVertexAlgebra.translation a := by
    rw [A.conformal_translation]
  have hν1 : mode A.fields A.conformalVector 1 a = (d : ℂ) • a :=
    A.virasoro_zero_on_grade ha
  have hν2 : mode A.fields A.conformalVector 2 a = 0 := hq
  have ht := congrArg (fun f : Module.End ℂ V => f c) (A.translation_covariance a (d : ℤ))
  simp only [LinearMap.smul_apply] at ht
  norm_num [Finset.sum_range_succ, hν0, hν1, hν2, mode_zero, mode_smul] at h
  simp only [ht, Int.cast_natCast] at h
  change mode A.fields A.conformalVector 2 (mode A.fields a (-1 + (d : ℤ) - 1) c) -
      mode A.fields a (-1 + (d : ℤ) - 1) (mode A.fields A.conformalVector 2 c) =
        (d : ℂ) • mode A.fields a (0 + (d : ℤ) - 1) c
  rw [show -1 + (d : ℤ) - 1 = d - 2 by omega, zero_add]
  convert h using 1
  module

 
def selfCommutator (a : V) (d : ℕ) (m : ℤ) : Module.End ℂ V :=
  A.physicalMode a d m * A.physicalMode a d (-m) -
    A.physicalMode a d (-m) * A.physicalMode a d m

@[simp]
theorem selfCommutator_apply (a : V) (d : ℕ) (m : ℤ) (c : V) :
    A.selfCommutator a d m c =
      A.physicalMode a d m (A.physicalMode a d (-m) c) -
        A.physicalMode a d (-m) (A.physicalMode a d m c) := rfl

 

theorem selfCommutator_eq_sum {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hd : 1 ≤ d) (m : ℕ) (c : V) :
    A.selfCommutator a d m c =
      ∑ j ∈ Finset.range (2 * d), ((m + d - 1).choose j : ℂ) •
        A.physicalMode (mode A.fields a j a) (2 * d - j - 1) 0 c := by
  have hm : ((m + d - 1 : ℕ) : ℤ) = (m : ℤ) + d - 1 := by omega
  simp only [selfCommutator_apply, physicalMode]
  rw [← hm, A.mode_commutator]
  simp only [Int.cast_natCast, Ring.choose_natCast]
  have he : (∑ᶠ j : ℕ, ((m + d - 1).choose j : ℂ) •
      mode A.fields (mode A.fields a j a) ((m + d - 1 : ℕ) + (-(m : ℤ) + d - 1) - j) c) =
      ∑ j ∈ Finset.range (2 * d), ((m + d - 1).choose j : ℂ) •
        mode A.fields (mode A.fields a j a) ((m + d - 1 : ℕ) + (-(m : ℤ) + d - 1) - j) c := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hjn
    have hz := A.mode_eq_zero_of_negative_energy ha ha (j : ℤ) (by omega)
    apply hj
    simp only [hz, mode_zero, LinearMap.zero_apply, smul_zero]
  rw [he]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  congr 3
  omega

 

theorem selfCommutator_eq_sum_reduced {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hd : 1 ≤ d) (m : ℕ) (v : V) :
    A.selfCommutator a d m v =
      ∑ j ∈ Finset.range (2 * d - 1),
        (((m + d - 1).choose (j + 1) : ℂ) - ((d - 1).choose (j + 1) : ℂ)) •
          A.physicalMode (mode A.fields a (j + 1) a) (2 * d - j - 2) 0 v := by
  have hzero := A.selfCommutator_eq_sum ha hd 0 v
  simp only [selfCommutator_apply, Nat.cast_zero, neg_zero, sub_self, zero_add] at hzero
  have he : 2 * d = (2 * d - 1) + 1 := by omega
  calc
    _ = (∑ j ∈ Finset.range (2 * d), ((m + d - 1).choose j : ℂ) •
          A.physicalMode (mode A.fields a j a) (2 * d - j - 1) 0 v) -
        ∑ j ∈ Finset.range (2 * d), ((d - 1).choose j : ℂ) •
          A.physicalMode (mode A.fields a j a) (2 * d - j - 1) 0 v := by
      rw [A.selfCommutator_eq_sum ha hd, ← hzero, sub_zero]
    _ = ∑ j ∈ Finset.range (2 * d),
        (((m + d - 1).choose j : ℂ) - ((d - 1).choose j : ℂ)) •
          A.physicalMode (mode A.fields a j a) (2 * d - j - 1) 0 v := by
      rw [← Finset.sum_sub_distrib]
      simp only [sub_smul]
    _ = _ := by
      rw [he, Finset.sum_range_succ']
      simp only [Nat.choose_zero_right, Nat.cast_one, sub_self, zero_smul, add_zero]
      apply Finset.sum_congr rfl
      intro j _
      congr 3

 

theorem selfCommutator_bound {B : ℕ → ℝ} (hB : ∀ N, 1 ≤ B N)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hd : 1 ≤ d)
    (H : ∀ j < 2 * d, A.BlockGrowth B (mode A.fields a j a)
      (2 * d - j - 1) (2 * d - j - 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ N m : ℕ, m ≤ N + 1 →
      ∀ h ≤ N, ∀ c ∈ A.grade h,
        ‖A.selfCommutator a d m c‖ ≤
          C * (1 + (N : ℝ)) ^ p * B N ^ (2 * d - 1) * ‖c‖ := by
  let s := Finset.range (2 * d)
  have H' : ∀ j ∈ s, A.BlockGrowth B (mode A.fields a j a)
      (2 * d - j - 1) (2 * d - 1) := by
    intro j hj
    exact A.blockGrowth_mono_weight hB (H j (Finset.mem_range.mp hj)) (by omega)
  obtain ⟨C, hC, p, hp⟩ := A.finite_blockGrowth_uniform hB s
    (fun j => mode A.fields a j a) (fun j => 2 * d - j - 1) (fun _ => 2 * d - 1) H'
  refine ⟨(2 * d : ℝ) * ((d : ℝ) + 1) ^ (2 * d) * C, by positivity, p + 2 * d, ?_⟩
  intro N m hm h hN c hc
  have hBN : 0 ≤ B N := zero_le_one.trans (hB N)
  have hN1 : 1 ≤ 1 + (N : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg N)
  have hbase : 1 ≤ ((d : ℝ) + 1) * (1 + (N : ℝ)) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hcoef (j : ℕ) (hj : j < 2 * d) :
      ((m + d - 1).choose j : ℝ) ≤ ((d : ℝ) + 1) ^ (2 * d) * (1 + (N : ℝ)) ^ (2 * d) := by
    have hn : (m + d - 1 : ℕ) ≤ (d + 1) * (N + 1) := by
      calc
        m + d - 1 ≤ m + d := Nat.sub_le _ _
        _ ≤ N + 1 + d := Nat.add_le_add_right hm d
        _ ≤ _ := by nlinarith
    calc
      _ ≤ ((m + d - 1 : ℕ) : ℝ) ^ j := by exact_mod_cast Nat.choose_le_pow (m + d - 1) j
      _ ≤ (((d : ℝ) + 1) * (1 + (N : ℝ))) ^ j := by
        apply pow_le_pow_left₀ (Nat.cast_nonneg _)
        exact_mod_cast (show m + d - 1 ≤ (d + 1) * (1 + N) by simpa only [Nat.add_comm] using hn)
      _ ≤ (((d : ℝ) + 1) * (1 + (N : ℝ))) ^ (2 * d) :=
        pow_le_pow_right₀ hbase (by omega)
      _ = _ := mul_pow _ _ _
  rw [A.selfCommutator_eq_sum ha hd]
  calc
    _ ≤ ∑ j ∈ Finset.range (2 * d), ‖((m + d - 1).choose j : ℂ) •
        A.physicalMode (mode A.fields a j a) (2 * d - j - 1) 0 c‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (2 * d),
        (((d : ℝ) + 1) ^ (2 * d) * (1 + (N : ℝ)) ^ (2 * d)) *
          (C * (1 + (N : ℝ)) ^ p * B N ^ (2 * d - 1) * ‖c‖) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_smul, Complex.norm_natCast]
      have hmode := hp j hj N h hN h hN c hc
      simp only [sub_self] at hmode
      exact mul_le_mul (hcoef j (Finset.mem_range.mp hj)) hmode (norm_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; rw [pow_add]; ring

 

def generatorMajorant (D : ℕ) (S : ℕ → Finset V) (N : ℕ) : ℝ :=
  1 + ∑ d ∈ Finset.range (D + 1), ∑ a ∈ S d,
    ∑ h ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ‖A.modeBlock a d h k‖ ^ (d : ℝ)⁻¹

theorem one_le_generatorMajorant (D : ℕ) (S : ℕ → Finset V) (N : ℕ) :
    1 ≤ A.generatorMajorant D S N := by
  dsimp [generatorMajorant]
  have : 0 ≤ ∑ d ∈ Finset.range (D + 1), ∑ a ∈ S d,
      ∑ h ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
        ‖A.modeBlock a d h k‖ ^ (d : ℝ)⁻¹ := by
    positivity
  linarith

theorem root_modeBlock_le_generatorMajorant (D : ℕ) (S : ℕ → Finset V)
    {d h k N : ℕ} {a : V} (hd : d ≤ D) (ha : a ∈ S d)
    (hh : h ≤ N) (hk : k ≤ N) :
    ‖A.modeBlock a d h k‖ ^ (d : ℝ)⁻¹ ≤ A.generatorMajorant D S N := by
  have H (e : ℕ) (b : V) (i j : ℕ) :
      0 ≤ ‖A.modeBlock b e i j‖ ^ (e : ℝ)⁻¹ :=
    Real.rpow_nonneg (norm_nonneg (A.modeBlock b e i j)) _
  have Hk (e : ℕ) (b : V) (i : ℕ) : 0 ≤
      ∑ j ∈ Finset.range (N + 1), ‖A.modeBlock b e i j‖ ^ (e : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun j _ => H e b i j)
  have Hh (e : ℕ) (b : V) : 0 ≤
      ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
        ‖A.modeBlock b e i j‖ ^ (e : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun i _ => Hk e b i)
  have Ha (e : ℕ) : 0 ≤ ∑ b ∈ S e,
      ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
        ‖A.modeBlock b e i j‖ ^ (e : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun b _ => Hh e b)
  have h₁ := Finset.single_le_sum (s := Finset.range (N + 1)) (a := k)
    (fun j _ => H d a h j) (Finset.mem_range.mpr (by omega))
  have h₂ := Finset.single_le_sum (s := Finset.range (N + 1)) (a := h)
    (fun i _ => Hk d a i) (Finset.mem_range.mpr (by omega))
  have h₃ := Finset.single_le_sum (s := S d) (a := a) (fun b _ => Hh d b) ha
  have h₄ := Finset.single_le_sum (s := Finset.range (D + 1)) (a := d)
    (fun e _ => Ha e) (Finset.mem_range.mpr (by omega))
  exact (h₁.trans (h₂.trans (h₃.trans h₄))).trans (le_add_of_nonneg_left zero_le_one)

theorem generator_blockGrowth (D : ℕ) (S : ℕ → Finset V)
    {d : ℕ} {a : V} (hd : 0 < d) (hD : d ≤ D) (ha : a ∈ S d) :
    A.BlockGrowth (A.generatorMajorant D S) a d d := by
  refine ⟨1, zero_le_one, 0, fun N h hh k hk c hc => ?_⟩
  have hnorm := A.root_modeBlock_le_generatorMajorant D S hD ha hh hk
  have ht : 0 ≤ ‖A.modeBlock a d h k‖ ^ (d : ℝ)⁻¹ :=
    Real.rpow_nonneg (norm_nonneg (A.modeBlock a d h k)) _
  have hpow := pow_le_pow_left₀ ht hnorm d
  rw [Real.rpow_inv_natCast_pow (x := ‖A.modeBlock a d h k‖) (n := d)
    (norm_nonneg (A.modeBlock a d h k)) (by omega)] at hpow
  have h := (A.modeBlock a d h k).le_opNorm (⟨c, hc⟩ : A.grade h)
  simpa only [pow_zero, mul_one, one_mul, modeBlock_apply, ← Submodule.norm_coe] using
    h.trans (mul_le_mul_of_nonneg_right hpow (norm_nonneg c))

 

structure UnitaryStructure where
  pct : V →ₛₗ[starRingEnd ℂ] V
  pct_involutive : Function.Involutive pct
  pct_vacuum : pct A.vacuum = A.vacuum
  pct_conformal : pct A.conformalVector = A.conformalVector
  pct_modes : ∀ (a b : V) (n : ℤ),
    pct (mode A.fields a n b) = mode A.fields (pct a) n (pct b)
  vacuum_norm : ‖A.vacuum‖ = 1
  invariant : ∀ d : ℕ, ∀ a ∈ A.grade d, ∀ n : ℤ, ∀ b c : V,
    inner ℂ (mode A.fields a n b) c =
      inner ℂ b (((-1 : ℂ) ^ d) •
        ∑ j ∈ Finset.range (d + 1), ((j.factorial : ℂ)⁻¹) •
          mode A.fields ((A.virasoroMode 1 ^ j) (pct a))
            (2 * (d : ℤ) - j - n - 2) c)

namespace UnitaryStructure

variable {A} (U : A.UnitaryStructure)

 
def IsHermitian (d : ℕ) (a : V) : Prop := ((-1 : ℂ) ^ d) • U.pct a = a

 
theorem pct_virasoro (a : V) (n : ℤ) :
    U.pct (A.virasoroMode n a) = A.virasoroMode n (U.pct a) := by
  simpa [virasoroMode, U.pct_conformal] using U.pct_modes A.conformalVector a (n + 1)

 
theorem pct_quasiPrimary {a : V} (ha : A.IsQuasiPrimary a) :
    A.IsQuasiPrimary (U.pct a) := by
  change A.virasoroMode 1 (U.pct a) = 0
  rw [← U.pct_virasoro, ha, map_zero]

 

theorem physicalMode_adjoint {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    (m : ℤ) (b c : V) :
    inner ℂ (A.physicalMode a d m b) c =
      inner ℂ b (A.physicalMode a d (-m) c) := by
  have hp : A.virasoroMode 1 (U.pct a) = 0 := U.pct_quasiPrimary hq
  have hpj (j : ℕ) (hj : j ≠ 0) :
      (A.virasoroMode 1 ^ j) (U.pct a) = 0 := by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    rw [pow_succ, Module.End.mul_apply, hp, map_zero]
  have hs :
      (∑ j ∈ Finset.range (d + 1), ((j.factorial : ℂ)⁻¹) •
        mode A.fields ((A.virasoroMode 1 ^ j) (U.pct a))
          (2 * (d : ℤ) - j - (m + d - 1) - 2) c) =
      mode A.fields (U.pct a) (2 * (d : ℤ) - (m + d - 1) - 2) c := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      simp [hpj j hj]
    · simp
  have h := U.invariant d a ha (m + d - 1) b c
  rw [hs] at h
  have he :
      ((-1 : ℂ)^d) •
        mode A.fields (U.pct a) (2 * (d : ℤ) - (m + d - 1) - 2) c =
      mode A.fields a (2 * (d : ℤ) - (m + d - 1) - 2) c := by
    rw [← LinearMap.smul_apply, ← mode_smul, hh]
  rw [he] at h
  have hi : 2 * (d : ℤ) - (m + d - 1) - 2 = -m + d - 1 := by omega
  simpa only [physicalMode, hi] using h

include U

 

theorem mode_norm_sq_difference {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) (m : ℤ) (c : V) :
    ‖A.physicalMode a d (-m) c‖ ^ 2 - ‖A.physicalMode a d m c‖ ^ 2 =
      (inner ℂ c (A.selfCommutator a d m c)).re := by
  have hp := U.physicalMode_adjoint ha hq hh (-m) c (A.physicalMode a d (-m) c)
  simp only [neg_neg] at hp
  have hn := U.physicalMode_adjoint ha hq hh m c (A.physicalMode a d m c)
  rw [selfCommutator_apply, inner_sub_right, ← hp, ← hn, Complex.sub_re]
  exact (congrArg₂ (fun x y : ℝ => x - y)
    (inner_self_eq_norm_sq (𝕜 := ℂ) (A.physicalMode a d (-m) c))
    (inner_self_eq_norm_sq (𝕜 := ℂ) (A.physicalMode a d m c))).symm

 
theorem mode_norm_sq_le_adjoint {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) (m : ℤ) (c : V) :
    ‖A.physicalMode a d m c‖ ^ 2 ≤
      ‖c‖ * ‖A.physicalMode a d (-m) (A.physicalMode a d m c)‖ := by
  have h := congrArg Complex.re
    (U.physicalMode_adjoint ha hq hh m c (A.physicalMode a d m c))
  rw [inner_self_eq_norm_sq_to_K] at h
  norm_cast at h
  exact h.trans_le ((Complex.re_le_norm _).trans (norm_inner_le_norm _ _))
end UnitaryStructure
end CFTTypeVOA
end StronglyRationalVOA

end

end OAI
