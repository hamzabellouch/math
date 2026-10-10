import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.BlockGrowth

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U
theorem lowering_norm_sq_of_commutator {a : V} {d m N : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    (hm : 0 < m) {R : ℝ} (hR : 0 ≤ R)
    (H : ∀ h ≤ N, ∀ c ∈ A.grade h, ‖A.selfCommutator a d m c‖ ≤ R * ‖c‖) :
    ∀ h ≤ N, ∀ c ∈ A.grade h,
      ‖A.physicalMode a d m c‖ ^ 2 ≤ (h : ℝ) * R * ‖c‖ ^ 2 := by
  intro h
  induction h using Nat.strong_induction_on with
  | h h ih =>
    intro hN c hc
    by_cases hhm : h < m
    · have hz : A.physicalMode a d m c = 0 :=
        A.mode_eq_zero_of_negative_energy ha hc ((m : ℤ) + d - 1) (by omega)
      rw [hz, norm_zero, zero_pow (by omega)]
      positivity
    · let e := h - m
      have heh : e < h := by dsimp [e]; omega
      have heN : e ≤ N := by omega
      have hb : A.physicalMode a d m c ∈ A.grade e :=
        A.mode_mem_grade ha hc ((m : ℤ) + d - 1) (by dsimp [e]; omega)
      have hi := ih e heh heN _ hb
      have hcom : (inner ℂ (A.physicalMode a d m c)
          (A.selfCommutator a d m (A.physicalMode a d m c))).re ≤
          R * ‖A.physicalMode a d m c‖ ^ 2 := by
        calc
          _ ≤ ‖inner ℂ (A.physicalMode a d m c)
              (A.selfCommutator a d m (A.physicalMode a d m c))‖ := Complex.re_le_norm _
          _ ≤ ‖A.physicalMode a d m c‖ *
              ‖A.selfCommutator a d m (A.physicalMode a d m c)‖ := norm_inner_le_norm _ _
          _ ≤ ‖A.physicalMode a d m c‖ * (R * ‖A.physicalMode a d m c‖) := by
            gcongr
            exact H e heN _ hb
          _ = _ := by ring
      have hdiff := U.mode_norm_sq_difference ha hq hh (m : ℤ) (A.physicalMode a d m c)
      have hecast : (e : ℝ) + 1 ≤ h := by exact_mod_cast (by omega : e + 1 ≤ h)
      have hraise : ‖A.physicalMode a d (-(m : ℤ)) (A.physicalMode a d m c)‖ ^ 2 ≤
          (h : ℝ) * R * ‖A.physicalMode a d m c‖ ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_right hecast
          (mul_nonneg hR (sq_nonneg ‖A.physicalMode a d m c‖))
        nlinarith
      have hcs := U.mode_norm_sq_le_adjoint ha hq hh (m : ℤ) c
      by_cases hz : ‖A.physicalMode a d m c‖ = 0
      · rw [hz, zero_pow (by omega)]
        positivity
      · have hp : 0 < ‖A.physicalMode a d m c‖ ^ 2 := sq_pos_of_ne_zero hz
        apply (mul_le_mul_iff_of_pos_right hp).mp
        calc
          _ ≤ (‖c‖ * ‖A.physicalMode a d (-(m : ℤ)) (A.physicalMode a d m c)‖) ^ 2 := by
            nlinarith [sq_nonneg (‖c‖ * ‖A.physicalMode a d (-(m : ℤ)) (A.physicalMode a d m c)‖ -
              ‖A.physicalMode a d m c‖ ^ 2)]
          _ = ‖c‖ ^ 2 * ‖A.physicalMode a d (-(m : ℤ)) (A.physicalMode a d m c)‖ ^ 2 := mul_pow _ _ _
          _ ≤ ‖c‖ ^ 2 * ((h : ℝ) * R * ‖A.physicalMode a d m c‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hraise (sq_nonneg _)
          _ = _ := by ring

 

theorem raising_norm_sq_of_commutator {a : V} {d m N : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    (hm : 0 < m) {R : ℝ} (hR : 0 ≤ R)
    (H : ∀ h ≤ N, ∀ c ∈ A.grade h, ‖A.selfCommutator a d m c‖ ≤ R * ‖c‖)
    {h : ℕ} (hN : h ≤ N) {c : V} (hc : c ∈ A.grade h) :
    ‖A.physicalMode a d (-(m : ℤ)) c‖ ^ 2 ≤ ((h : ℝ) + 1) * R * ‖c‖ ^ 2 := by
  have hi := U.lowering_norm_sq_of_commutator ha hq hh hm hR H h hN c hc
  have hdiff := U.mode_norm_sq_difference ha hq hh (m : ℤ) c
  have hcom : (inner ℂ c (A.selfCommutator a d m c)).re ≤ R * ‖c‖ ^ 2 := by
    calc
      _ ≤ ‖inner ℂ c (A.selfCommutator a d m c)‖ := Complex.re_le_norm _
      _ ≤ ‖c‖ * ‖A.selfCommutator a d m c‖ := norm_inner_le_norm _ _
      _ ≤ ‖c‖ * (R * ‖c‖) := mul_le_mul_of_nonneg_left (H h hN c hc) (norm_nonneg _)
      _ = _ := by ring
  nlinarith

 
theorem virasoro_adjoint (m : ℤ) (a b : V) :
    inner ℂ (A.virasoroMode m a) b = inner ℂ a (A.virasoroMode (-m) b) := by
  have hh : U.IsHermitian 2 A.conformalVector := by
    simp [IsHermitian, U.pct_conformal]
  simpa only [A.physicalMode_conformal] using
    U.physicalMode_adjoint A.conformal_mem A.conformal_quasiPrimary hh m a b

 

theorem grades_orthogonal {d e : ℕ} (hde : d ≠ e) {a b : V}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) : inner ℂ a b = 0 := by
  have h := U.virasoro_adjoint 0 a b
  simp only [neg_zero, A.virasoro_zero_on_grade ha, A.virasoro_zero_on_grade hb,
    inner_smul_left, inner_smul_right, map_natCast] at h
  have hd : (d : ℂ) - e ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hde)
  apply (mul_eq_zero.mp (show ((d : ℂ) - e) * inner ℂ a b = 0 from ?_)).resolve_left hd
  rw [sub_mul, h, sub_self]

 

theorem centralCharge_eq : A.centralCharge = 2 * (‖A.conformalVector‖ : ℂ)^2 := by
  have h := U.virasoro_adjoint (-2) A.vacuum A.conformalVector
  norm_num at h
  rw [← A.conformal_eq_virasoro_vacuum, A.virasoro_two_conformal,
    inner_smul_right, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
    U.vacuum_norm] at h
  norm_num at h
  linear_combination -2 * h

 
theorem centralCharge_nonneg : A.centralCharge.im = 0 ∧ 0 ≤ A.centralCharge.re := by
  rw [U.centralCharge_eq]
  constructor
  · simp [pow_two]
  · simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
      mul_zero, zero_mul, sub_zero]
    positivity

 
theorem grade_orthogonalFamily :
    OrthogonalFamily ℂ (fun d => A.grade d) (fun d => (A.grade d).subtypeₗᵢ) := by
  intro d e hde a b
  exact U.grades_orthogonal hde a.property b.property

 
theorem norm_sq_eq_sum_grades (a : V) :
    ‖a‖ ^ 2 = ∑ d ∈ A.gradeSupport a, ‖A.gradeComponent d a‖ ^ 2 := by
  have h := U.grade_orthogonalFamily.norm_sum (fun d => A.gradingEquiv a d)
    (A.gradeSupport a)
  change ‖∑ d ∈ A.gradeSupport a, A.gradeComponent d a‖ ^ 2 =
    ∑ d ∈ A.gradeSupport a, ‖A.gradeComponent d a‖ ^ 2 at h
  rwa [A.sum_gradeComponents] at h

 
theorem energy_norm_sq_eq_sum_grades (a : V) (k : ℕ) :
    ‖(A.energyShift ^ k) a‖ ^ 2 =
      ∑ d ∈ A.gradeSupport a, ((1 + (d : ℝ)) ^ k * ‖A.gradeComponent d a‖) ^ 2 := by
  have h := U.grade_orthogonalFamily.norm_sum
    (fun d => ⟨(A.energyShift ^ k) (A.gradeComponent d a), by
      rw [A.energyShift_pow_on_grade (A.gradeComponent_mem d a)]
      exact (A.grade d).smul_mem _ (A.gradeComponent_mem d a)⟩)
    (A.gradeSupport a)
  change ‖∑ d ∈ A.gradeSupport a, (A.energyShift ^ k) (A.gradeComponent d a)‖ ^ 2 =
    ∑ d ∈ A.gradeSupport a, ‖(A.energyShift ^ k) (A.gradeComponent d a)‖ ^ 2 at h
  rw [← map_sum, A.sum_gradeComponents] at h
  simpa only [A.energyShift_pow_norm_on_grade (A.gradeComponent_mem _ _)] using h

 

theorem virasoro_norm_sq_identity (n : ℤ) {d : ℕ} {a : V}
    (ha : a ∈ A.grade d) :
    ‖A.virasoroMode (-n) a‖ ^ 2 = ‖A.virasoroMode n a‖ ^ 2 +
      (2 * (n : ℝ) * d + A.centralCharge.re / 12 * ((n : ℝ)^3 - n)) * ‖a‖ ^ 2 := by
  have h := congrArg (fun b : V => inner ℂ a b) (A.virasoro_commutator n (-n) a)
  have hn := U.virasoro_adjoint (-n) a (A.virasoroMode (-n) a)
  simp only [neg_neg] at hn
  rw [inner_sub_right, ← hn, ← U.virasoro_adjoint n a (A.virasoroMode n a)] at h
  simp only [add_neg_cancel, A.virasoro_zero_on_grade ha,
    inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K] at h
  have hr := congrArg Complex.re h
  norm_num [Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, pow_succ] at hr
  nlinarith [hr]

 
theorem virasoro_norm_sq_le_adjoint (n : ℤ) (a : V) :
    ‖A.virasoroMode n a‖ ^ 2 ≤ ‖a‖ * ‖A.virasoroMode (-n) (A.virasoroMode n a)‖ := by
  have h := congrArg Complex.re (U.virasoro_adjoint n a (A.virasoroMode n a))
  rw [inner_self_eq_norm_sq_to_K] at h
  norm_cast at h
  calc
    _ = (inner ℂ a (A.virasoroMode (-n) (A.virasoroMode n a))).re := h
    _ ≤ ‖inner ℂ a (A.virasoroMode (-n) (A.virasoroMode n a))‖ := Complex.re_le_norm _
    _ ≤ _ := norm_inner_le_norm _ _

 

theorem virasoro_positive_norm_sq (n : ℕ) (hn : 0 < n) (d : ℕ)
    (a : V) (ha : a ∈ A.grade d) :
    ‖A.virasoroMode (n : ℤ) a‖ ^ 2 ≤
      (1 + A.centralCharge.re * n) * (d : ℝ)^2 * ‖a‖ ^ 2 := by
  induction d using Nat.strong_induction_on generalizing a with
  | h d ih =>
    by_cases hd : d < n
    · rw [A.virasoro_eq_zero_of_lt ha n (by exact_mod_cast hd), norm_zero, zero_pow (by omega)]
      have hc := U.centralCharge_nonneg.2
      positivity
    · let e := d - n
      have hen : e + n = d := Nat.sub_add_cancel (Nat.le_of_not_gt hd)
      have he : e < d := by dsimp [e]; omega
      have hb : A.virasoroMode (n : ℤ) a ∈ A.grade e :=
        A.virasoro_mem_grade ha n (by omega)
      have hi := ih e he (A.virasoroMode (n : ℤ) a) hb
      have hc := U.centralCharge_nonneg.2
      have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have her : (0 : ℝ) ≤ e := Nat.cast_nonneg e
      have hdr : (d : ℝ) = e + n := by exact_mod_cast hen.symm
      have hq : A.centralCharge.re / 12 * ((n : ℝ)^3 - n) ≤
          A.centralCharge.re * (n : ℝ)^3 := by
        nlinarith [mul_nonneg hc (pow_nonneg hnr 3), mul_nonneg hc hnr]
      have hcoeff : (1 + A.centralCharge.re * n) * (e : ℝ)^2 +
          (2 * (n : ℝ) * e + A.centralCharge.re / 12 * ((n : ℝ)^3 - n)) ≤
          (1 + A.centralCharge.re * n) * (d : ℝ)^2 := by
        rw [hdr]
        nlinarith [sq_nonneg (n : ℝ), mul_nonneg (mul_nonneg hc (sq_nonneg (n : ℝ))) her]
      have hraise : ‖A.virasoroMode (-(n : ℤ)) (A.virasoroMode n a)‖ ^ 2 ≤
          ((1 + A.centralCharge.re * n) * (d : ℝ)^2) * ‖A.virasoroMode n a‖ ^ 2 := by
        rw [U.virasoro_norm_sq_identity (n : ℤ) hb]
        push_cast
        calc
          _ ≤ ((1 + A.centralCharge.re * n) * (e : ℝ)^2) * ‖A.virasoroMode n a‖ ^ 2 +
              (2 * (n : ℝ) * e + A.centralCharge.re / 12 * ((n : ℝ)^3 - n)) *
                ‖A.virasoroMode n a‖ ^ 2 := add_le_add hi le_rfl
          _ = ((1 + A.centralCharge.re * n) * (e : ℝ)^2 +
              (2 * (n : ℝ) * e + A.centralCharge.re / 12 * ((n : ℝ)^3 - n))) *
                ‖A.virasoroMode n a‖ ^ 2 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
      have hcs := U.virasoro_norm_sq_le_adjoint (n : ℤ) a
      by_cases hz : ‖A.virasoroMode (n : ℤ) a‖ = 0
      · rw [hz, zero_pow (by omega)]
        positivity
      · have hp : 0 < ‖A.virasoroMode (n : ℤ) a‖ ^ 2 := sq_pos_of_ne_zero hz
        apply (mul_le_mul_iff_of_pos_right hp).mp
        calc
          _ ≤ (‖a‖ * ‖A.virasoroMode (-(n : ℤ)) (A.virasoroMode n a)‖) ^ 2 := by
            nlinarith [sq_nonneg (‖a‖ * ‖A.virasoroMode (-(n : ℤ)) (A.virasoroMode n a)‖ -
              ‖A.virasoroMode (n : ℤ) a‖ ^ 2)]
          _ = ‖a‖ ^ 2 * ‖A.virasoroMode (-(n : ℤ)) (A.virasoroMode n a)‖ ^ 2 := mul_pow _ _ _
          _ ≤ ‖a‖ ^ 2 * (((1 + A.centralCharge.re * n) * (d : ℝ)^2) *
              ‖A.virasoroMode n a‖ ^ 2) := mul_le_mul_of_nonneg_left hraise (sq_nonneg _)
          _ = _ := by ring

 
theorem virasoro_negative_norm_sq (n : ℕ) (hn : 0 < n) (d : ℕ)
    (a : V) (ha : a ∈ A.grade d) :
    ‖A.virasoroMode (-(n : ℤ)) a‖ ^ 2 ≤
      (1 + A.centralCharge.re * n) * ((d : ℝ) + n)^2 * ‖a‖ ^ 2 := by
  have hi := U.virasoro_positive_norm_sq n hn d a ha
  have hc := U.centralCharge_nonneg.2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hq : A.centralCharge.re / 12 * ((n : ℝ)^3 - n) ≤
      A.centralCharge.re * (n : ℝ)^3 := by
    nlinarith [mul_nonneg hc (pow_nonneg hn0 3), mul_nonneg hc hn0]
  have hcoeff : (1 + A.centralCharge.re * n) * (d : ℝ)^2 +
      (2 * (n : ℝ) * d + A.centralCharge.re / 12 * ((n : ℝ)^3 - n)) ≤
      (1 + A.centralCharge.re * n) * ((d : ℝ) + n)^2 := by
    nlinarith [sq_nonneg (n : ℝ), mul_nonneg (mul_nonneg hc (sq_nonneg (n : ℝ))) hd0]
  rw [U.virasoro_norm_sq_identity (n : ℤ) ha]
  push_cast
  calc
    _ ≤ ((1 + A.centralCharge.re * n) * (d : ℝ)^2) * ‖a‖ ^ 2 +
        (2 * (n : ℝ) * d + A.centralCharge.re / 12 * ((n : ℝ)^3 - n)) * ‖a‖ ^ 2 :=
      add_le_add hi le_rfl
    _ = ((1 + A.centralCharge.re * n) * (d : ℝ)^2 +
        (2 * (n : ℝ) * d + A.centralCharge.re / 12 * ((n : ℝ)^3 - n))) * ‖a‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)

 

theorem virasoro_level_coefficient_le (n d : ℕ) :
    (1 + A.centralCharge.re * n) * ((d : ℝ) + n)^2 ≤
      ((1 + A.centralCharge.re) * (1 + (n : ℝ))^2 * (1 + (d : ℝ)))^2 := by
  have hc := U.centralCharge_nonneg.2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hc1 : 1 ≤ (1 + A.centralCharge.re) * (1 + (n : ℝ)) := by nlinarith
  have hk : 1 + A.centralCharge.re * n ≤
      ((1 + A.centralCharge.re) * (1 + (n : ℝ)))^2 := by
    have hle : 1 + A.centralCharge.re * n ≤
        (1 + A.centralCharge.re) * (1 + (n : ℝ)) := by nlinarith
    nlinarith [sq_nonneg ((1 + A.centralCharge.re) * (1 + (n : ℝ)) - 1)]
  have hd : (d : ℝ) + n ≤ (1 + (n : ℝ)) * (1 + (d : ℝ)) := by nlinarith
  calc
    _ ≤ ((1 + A.centralCharge.re) * (1 + (n : ℝ)))^2 *
        ((1 + (n : ℝ)) * (1 + (d : ℝ)))^2 := by gcongr
    _ = _ := by ring

 

theorem virasoro_norm_on_grade (n : ℤ) {d : ℕ} {a : V} (ha : a ∈ A.grade d) :
    ‖A.virasoroMode n a‖ ≤
      (1 + A.centralCharge.re) * (1 + |(n : ℝ)|)^2 * (1 + (d : ℝ)) * ‖a‖ := by
  have hc := U.centralCharge_nonneg.2
  have hsuff (k : ℕ) (h : ‖A.virasoroMode n a‖ ^ 2 ≤
      (1 + A.centralCharge.re * k) * ((d : ℝ) + k)^2 * ‖a‖ ^ 2)
      (hk : |(n : ℝ)| = k) : ‖A.virasoroMode n a‖ ≤
      (1 + A.centralCharge.re) * (1 + |(n : ℝ)|)^2 * (1 + (d : ℝ)) * ‖a‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [hk, mul_pow]
    exact h.trans (mul_le_mul_of_nonneg_right (U.virasoro_level_coefficient_le k d) (sq_nonneg _))
  cases n with
  | ofNat k =>
    cases k with
    | zero =>
      have he0 : Int.ofNat 0 = 0 := by decide
      rw [he0, Int.cast_zero]
      change ‖A.virasoroMode 0 a‖ ≤
        (1 + A.centralCharge.re) * (1 + |(0 : ℝ)|)^2 * (1 + (d : ℝ)) * ‖a‖
      rw [A.virasoro_zero_on_grade ha, norm_smul]
      simp only [norm_natCast, abs_zero, add_zero, one_pow, mul_one]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg a)
      nlinarith [mul_nonneg hc (Nat.cast_nonneg d)]
    | succ k =>
      apply hsuff (k + 1) _ (by
        change |((k + 1 : ℕ) : ℝ)| = ((k + 1 : ℕ) : ℝ)
        exact abs_of_nonneg (Nat.cast_nonneg _))
      have h := U.virasoro_positive_norm_sq (k + 1) (by omega) d a ha
      apply h.trans
      gcongr
      exact le_add_of_nonneg_right (by positivity)
  | negSucc k =>
    have he : Int.negSucc k = -((k + 1 : ℕ) : ℤ) := by omega
    apply hsuff (k + 1) _ (by
      rw [he, Int.cast_neg, Int.cast_natCast, abs_neg]
      exact abs_of_nonneg (Nat.cast_nonneg _))
    rw [he]
    exact U.virasoro_negative_norm_sq (k + 1) (by omega) d a ha

 

theorem mode_images_orthogonal {w d e : ℕ} {a b c : V}
    (ha : a ∈ A.grade w) (hb : b ∈ A.grade d) (hc : c ∈ A.grade e)
    (hde : d ≠ e) (n : ℤ) : inner ℂ (mode A.fields a n b) (mode A.fields a n c) = 0 := by
  have h := U.virasoro_adjoint 0 (mode A.fields a n b) (mode A.fields a n c)
  simp only [neg_zero, A.mode_energy_eigenvalue ha hb, A.mode_energy_eigenvalue ha hc,
    inner_smul_left, inner_smul_right, map_sub, map_add, map_natCast, map_intCast, map_one] at h
  have hd : ((d : ℂ) + w - n - 1) - ((e : ℂ) + w - n - 1) ≠ 0 := by
    intro hz
    have hcast : (d : ℂ) = e := by linear_combination hz
    exact hde (by exact_mod_cast hcast)
  apply (mul_eq_zero.mp (show (((d : ℂ) + w - n - 1) - ((e : ℂ) + w - n - 1)) *
      inner ℂ (mode A.fields a n b) (mode A.fields a n c) = 0 from ?_)).resolve_left hd
  rw [sub_mul, h, sub_self]

 

theorem mode_norm_sq_eq_sum_grades {w : ℕ} {a : V} (ha : a ∈ A.grade w)
    (n : ℤ) (b : V) :
    ‖mode A.fields a n b‖ ^ 2 =
      ∑ d ∈ A.gradeSupport b, ‖mode A.fields a n (A.gradeComponent d b)‖ ^ 2 := by
  classical
  let f := fun d => mode A.fields a n (A.gradeComponent d b)
  have hsum : ∑ d ∈ A.gradeSupport b, f d = mode A.fields a n b := by
    dsimp only [f]
    rw [← map_sum, A.sum_gradeComponents]
  have h : inner ℂ (∑ d ∈ A.gradeSupport b, f d) (∑ d ∈ A.gradeSupport b, f d) =
      ∑ d ∈ A.gradeSupport b, inner ℂ (f d) (f d) := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro d hd
    rw [inner_sum]
    apply Finset.sum_eq_single d
    · intro e _ hed
      exact U.mode_images_orthogonal ha (A.gradeComponent_mem d b)
        (A.gradeComponent_mem e b) (Ne.symm hed) n
    · exact fun hnot => (hnot hd).elim
  rw [hsum] at h
  simp only [inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

 

theorem zeroMode_norm_sq_of_commutator {a : V} {d N : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    (hd : 1 ≤ d) {R : ℝ} (hR : 0 ≤ R)
    (H : ∀ h ≤ N, ∀ c ∈ A.grade h, ‖A.selfCommutator a d (1 : ℕ) c‖ ≤ R * ‖c‖)
    {h : ℕ} (hN : h ≤ N) {c : V} (hc : c ∈ A.grade h) :
    ‖A.physicalMode a d 0 c‖ ^ 2 ≤
      256 * (1 + A.centralCharge.re)^2 * (1 + (N : ℝ))^3 * R * ‖c‖^2 := by
  let G : ℝ := Real.sqrt ((1 + (N : ℝ)) * R)
  let K : ℝ := 8 * (1 + A.centralCharge.re) * (1 + (N : ℝ))
  have hccharge := U.centralCharge_nonneg.2
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hG : 0 ≤ G := Real.sqrt_nonneg _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hraising {e : ℕ} (he : e ≤ N) {b : V} (hb : b ∈ A.grade e) :
      ‖A.physicalMode a d (-1) b‖ ≤ G * ‖b‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hG (norm_nonneg _))).mp
    have h := U.raising_norm_sq_of_commutator ha hq hh (by omega : 0 < 1) hR H he hb
    norm_num only [Nat.cast_one, neg_inj] at h
    rw [mul_pow, show G ^ 2 = (1 + (N : ℝ)) * R from Real.sq_sqrt (by positivity)]
    calc
      _ ≤ ((e : ℝ) + 1) * R * ‖b‖ ^ 2 := h
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : e + 1 ≤ 1 + N)) hR)
        (sq_nonneg _)
  have hLbound {e : ℕ} (he : e ≤ N + 1) {b : V} (hb : b ∈ A.grade e) :
      ‖A.virasoroMode 1 b‖ ≤ K * ‖b‖ := by
    have h := U.virasoro_norm_on_grade 1 hb
    norm_num only [Int.cast_one, abs_one, one_add_one_eq_two, Nat.reducePow] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have her : (e : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast he
    dsimp [K]
    nlinarith [mul_nonneg (show 0 ≤ 1 + A.centralCharge.re by linarith) (by linarith : 0 ≤ 2 * (1 + (N : ℝ)) - (1 + e))]
  have hraisegrade : A.physicalMode a d (-1) c ∈ A.grade (h + 1) :=
    A.mode_mem_grade ha hc (-1 + (d : ℤ) - 1) (by omega)
  have hLgrade : A.virasoroMode 1 c ∈ A.grade (h - 1) := by
    by_cases hz : h = 0
    · have he := A.virasoro_eq_zero_of_lt hc 1 (by omega)
      rw [he]
      exact (A.grade (h - 1)).zero_mem
    · exact A.virasoro_mem_grade hc 1 (by omega)
  have hfirst : ‖A.virasoroMode 1 (A.physicalMode a d (-1) c)‖ ≤ K * G * ‖c‖ := by
    calc
      _ ≤ K * ‖A.physicalMode a d (-1) c‖ := hLbound (by omega) hraisegrade
      _ ≤ K * (G * ‖c‖) := mul_le_mul_of_nonneg_left (hraising hN hc) hK
      _ = _ := by ring
  have hsecond : ‖A.physicalMode a d (-1) (A.virasoroMode 1 c)‖ ≤ K * G * ‖c‖ := by
    calc
      _ ≤ G * ‖A.virasoroMode 1 c‖ := hraising (by omega) hLgrade
      _ ≤ G * (K * ‖c‖) := mul_le_mul_of_nonneg_left (hLbound (by omega) hc) hG
      _ = _ := by ring
  have he := congrArg norm (A.zeroMode_commutator ha hq c)
  rw [norm_smul, Complex.norm_natCast] at he
  have hlo : ‖A.physicalMode a d 0 c‖ ≤ 2 * K * G * ‖c‖ := by
    calc
      _ ≤ (d : ℝ) * ‖A.physicalMode a d 0 c‖ := by
        have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
        nlinarith [norm_nonneg (A.physicalMode a d 0 c)]
      _ = _ := he.symm
      _ ≤ ‖A.virasoroMode 1 (A.physicalMode a d (-1) c)‖ +
          ‖A.physicalMode a d (-1) (A.virasoroMode 1 c)‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  calc
    _ ≤ (2 * K * G * ‖c‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hlo 2
    _ = 4 * K^2 * G^2 * ‖c‖^2 := by ring
    _ = _ := by
      rw [show G^2 = (1 + (N : ℝ)) * R from Real.sq_sqrt (by positivity)]
      dsimp [K]
      ring

 

theorem modeBlock_norm_sq_bound {B : ℕ → ℝ} (hB : ∀ N, 1 ≤ B N)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hd : 1 ≤ d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    (H : ∀ j < 2 * d, A.BlockGrowth B (mode A.fields a j a)
      (2 * d - j - 1) (2 * d - j - 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ N h k : ℕ, h ≤ N → k ≤ N →
      ‖A.modeBlock a d h k‖ ^ 2 ≤ C * (1 + (N : ℝ)) ^ p * B N ^ (2 * d - 1) := by
  obtain ⟨C, hC, p, hp⟩ := A.selfCommutator_bound hB ha hd H
  let F : ℝ := 256 * (1 + A.centralCharge.re)^2
  have hccharge := U.centralCharge_nonneg.2
  have hF : 1 ≤ F := by dsimp [F]; nlinarith [sq_nonneg A.centralCharge.re]
  refine ⟨F * C, by positivity, p + 3, ?_⟩
  intro N h k hN kN
  let R : ℝ := C * (1 + (N : ℝ)) ^ p * B N ^ (2 * d - 1)
  let Q : ℝ := F * (1 + (N : ℝ)) ^ 3 * R
  have hBN : 0 ≤ B N := zero_le_one.trans (hB N)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hN1 : 1 ≤ 1 + (N : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg N)
  have hQle : (1 + (N : ℝ)) * R ≤ Q := by
    dsimp [Q]
    have hpow : 1 + (N : ℝ) ≤ (1 + (N : ℝ)) ^ 3 := by
      simpa only [pow_one] using pow_le_pow_right₀ hN1 (by norm_num : 1 ≤ 3)
    have hmul : (1 + (N : ℝ)) ^ 3 ≤ F * (1 + (N : ℝ)) ^ 3 := by
      nlinarith [pow_nonneg (show 0 ≤ 1 + (N : ℝ) by positivity) 3]
    exact mul_le_mul_of_nonneg_right (hpow.trans hmul) hR
  have H' (m : ℕ) (hm : m ≤ N + 1) :
      ∀ e ≤ N, ∀ c ∈ A.grade e, ‖A.selfCommutator a d m c‖ ≤ R * ‖c‖ := hp N m hm
  have hsquare (c : A.grade h) : ‖A.modeBlock a d h k c‖^2 ≤ Q * ‖c‖^2 := by
    rw [modeBlock_apply]
    by_cases heq : h = k
    · subst k
      simpa only [sub_self, Q, F, ← Submodule.norm_coe] using
        U.zeroMode_norm_sq_of_commutator ha hq hh hd hR (H' 1 (by omega)) hN c.property
    · by_cases hhk : k < h
      · let m := h - k
        have hm : 0 < m := by dsimp [m]; omega
        have hmN : m ≤ N + 1 := by dsimp [m]; omega
        have he : (m : ℤ) = (h : ℤ) - k := by dsimp [m]; omega
        have hb := U.lowering_norm_sq_of_commutator ha hq hh hm hR (H' m hmN) h hN c c.property
        rw [he] at hb
        apply hb.trans
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact (mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : h ≤ 1 + N)) hR).trans hQle
      · let m := k - h
        have hm : 0 < m := by dsimp [m]; omega
        have hmN : m ≤ N + 1 := by dsimp [m]; omega
        have he : -(m : ℤ) = (h : ℤ) - k := by dsimp [m]; omega
        have hb := U.raising_norm_sq_of_commutator ha hq hh hm hR (H' m hmN) hN c.property
        rw [he] at hb
        apply hb.trans
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        apply le_trans _ hQle
        apply mul_le_mul_of_nonneg_right _ hR
        exact_mod_cast (by omega : h + 1 ≤ 1 + N)
  have hop : ‖A.modeBlock a d h k‖ ≤ Real.sqrt Q := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro c
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hQ]
    exact hsquare c
  calc
    _ ≤ (Real.sqrt Q)^2 := pow_le_pow_left₀ (norm_nonneg (A.modeBlock a d h k)) hop 2
    _ = Q := Real.sq_sqrt hQ
    _ = _ := by dsimp [Q, R]; rw [pow_add]; ring
end UnitaryStructure
end CFTTypeVOA
end StronglyRationalVOA

end

end OAI
