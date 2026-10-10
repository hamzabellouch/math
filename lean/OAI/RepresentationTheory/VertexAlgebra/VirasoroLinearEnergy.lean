import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.BlockGrowth
import OAI.RepresentationTheory.VertexAlgebra.LoweringNormSq

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
theorem virasoro_linear_energy (n : ℤ) (a : V) :
    ‖A.virasoroMode n a‖ ≤
      (1 + A.centralCharge.re) * (1 + |(n : ℝ)|)^2 * ‖A.energyShift a‖ := by
  have hc := U.centralCharge_nonneg.2
  let K : ℝ := (1 + A.centralCharge.re) * (1 + |(n : ℝ)|)^2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mp
  change ‖A.virasoroMode n a‖ ^ 2 ≤ (K * ‖A.energyShift a‖)^2
  have hn := U.mode_norm_sq_eq_sum_grades A.conformal_mem (n + 1) a
  change ‖A.virasoroMode n a‖ ^ 2 =
    ∑ d ∈ A.gradeSupport a, ‖A.virasoroMode n (A.gradeComponent d a)‖ ^ 2 at hn
  have he := U.energy_norm_sq_eq_sum_grades a 1
  simp only [pow_one] at he
  calc
    _ = ∑ d ∈ A.gradeSupport a, ‖A.virasoroMode n (A.gradeComponent d a)‖ ^ 2 := hn
    _ ≤ ∑ d ∈ A.gradeSupport a, (K * (1 + (d : ℝ)) * ‖A.gradeComponent d a‖)^2 := by
      apply Finset.sum_le_sum
      intro d _
      exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
        (U.virasoro_norm_on_grade n (A.gradeComponent_mem d a))
    _ = K^2 * ∑ d ∈ A.gradeSupport a, ((1 + (d : ℝ)) * ‖A.gradeComponent d a‖)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = _ := by rw [← he]; ring

 

theorem conformal_energyBound : A.PolynomialEnergyBound A.conformalVector := by
  have hc := U.centralCharge_nonneg.2
  refine ⟨4 * (1 + A.centralCharge.re), by positivity, 2, 1, ?_⟩
  intro n b
  have hm : mode A.fields A.conformalVector n = A.virasoroMode (n - 1) := by
    unfold virasoroMode
    congr 1
    omega
  rw [hm]
  simp only [pow_one]
  have hidx : 1 + |((n - 1 : ℤ) : ℝ)| ≤ 2 * (1 + |(n : ℝ)|) := by
    push_cast
    have h := abs_sub (n : ℝ) 1
    norm_num at h
    nlinarith [abs_nonneg (n : ℝ)]
  calc
    _ ≤ (1 + A.centralCharge.re) * (1 + |((n - 1 : ℤ) : ℝ)|)^2 * ‖A.energyShift b‖ :=
      U.virasoro_linear_energy (n - 1) b
    _ ≤ (1 + A.centralCharge.re) * (2 * (1 + |(n : ℝ)|))^2 * ‖A.energyShift b‖ := by
      gcongr
    _ = _ := by ring

omit U in
 

theorem physical_normal_product (a b : V) (d : ℕ) :
    mode A.fields (mode A.fields a (-1) a) (2 * (d : ℤ) - 1) b =
      ∑ᶠ j : ℕ,
        (A.physicalMode a d (-(d + (j : ℤ))) (A.physicalMode a d (d + j) b) +
         A.physicalMode a d (d - 1 - j) (A.physicalMode a d (j + 1 - d) b)) := by
  rw [A.mode_normal_product]
  apply finsum_congr
  intro j
  simp only [physicalMode,
    show -((d : ℤ) + j) + d - 1 = -1 - j by omega,
    show (d : ℤ) + j + d - 1 = 2 * d - 1 + j by omega,
    show (d : ℤ) - 1 - j + d - 1 = 2 * d - 1 - 1 - j by omega,
    show (j : ℤ) + 1 - d + d - 1 = j by omega]

 

theorem normal_product_quadratic {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) (b : V) :
    (inner ℂ (mode A.fields (mode A.fields a (-1) a) (2 * (d : ℤ) - 1) b) b).re =
      ∑ᶠ j : ℕ,
        (‖A.physicalMode a d (d + j) b‖ ^ 2 +
         ‖A.physicalMode a d (j + 1 - d) b‖ ^ 2) := by
  let Q : V →+ ℝ :=
    { toFun := fun x => (inner ℂ x b).re
      map_zero' := by simp
      map_add' := by intro x y; simp }
  change Q _ = _
  rw [A.mode_normal_product,
    Q.map_finsum (A.mode_normal_product_hasFiniteSupport a a b (2 * (d : ℤ) - 1))]
  apply finsum_congr
  intro j
  have h₁ : mode A.fields a (-1 - j) = A.physicalMode a d (-(d + (j : ℤ))) := by
    dsimp [physicalMode]
    congr 1
    omega
  have h₂ : mode A.fields a (2 * (d : ℤ) - 1 + j) = A.physicalMode a d (d + j) := by
    dsimp [physicalMode]
    congr 1
    omega
  have h₃ : mode A.fields a (2 * (d : ℤ) - 1 - 1 - j) =
      A.physicalMode a d (-(j + 1 - d)) := by
    dsimp [physicalMode]
    congr 1
    omega
  have h₄ : mode A.fields a j = A.physicalMode a d (j + 1 - d) := by
    dsimp [physicalMode]
    congr 1
    omega
  dsimp [Q]
  rw [inner_add_left, Complex.add_re, h₁, h₂, h₃, h₄,
    U.physicalMode_adjoint ha hq hh (-(d + j)),
    U.physicalMode_adjoint ha hq hh (-(j + 1 - d))]
  simp only [neg_neg]
  exact congrArg₂ (· + ·) (inner_self_eq_norm_sq (𝕜 := ℂ) _) (inner_self_eq_norm_sq (𝕜 := ℂ) _)

omit U in
 

theorem normal_product_norms_hasFiniteSupport (a b : V) (d : ℕ) :
    Function.HasFiniteSupport (fun j : ℕ =>
        ‖A.physicalMode a d (d + j) b‖ ^ 2 +
        ‖A.physicalMode a d (j + 1 - d) b‖ ^ 2) := by
  have h₁ := mode_shift_hasFiniteSupport A.fields a b (2 * (d : ℤ) - 1)
  have h₂ := mode_shift_hasFiniteSupport A.fields a b 0
  apply (h₁.union h₂).subset
  intro j hj
  by_contra h
  have he₁ : mode A.fields a (2 * (d : ℤ) - 1 + j) b = 0 := by
    by_contra hn
    exact h (Or.inl hn)
  have he₂ : mode A.fields a (0 + j) b = 0 := by
    by_contra hn
    exact h (Or.inr hn)
  apply hj
  change ‖mode A.fields a (d + j + d - 1) b‖ ^ 2 +
        ‖mode A.fields a (j + 1 - d + d - 1) b‖ ^ 2 = 0
  rw [show (d : ℤ) + j + d - 1 = 2 * d - 1 + j by omega,
    show (j : ℤ) + 1 - d + d - 1 = 0 + j by omega, he₁, he₂]
  simp

 

theorem positive_column {a : V} {d : ℕ} (hd : 1 ≤ d) (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) (b : V) :
    (∑ᶠ m : ℕ, ‖A.physicalMode a d m b‖ ^ 2) ≤
      (inner ℂ (mode A.fields (mode A.fields a (-1) a) (2 * (d : ℤ) - 1) b) b).re := by
  rw [U.normal_product_quadratic ha hq hh]
  have hf : Function.HasFiniteSupport (fun m : ℕ => ‖A.physicalMode a d m b‖ ^ 2) := by
    have h := mode_shift_hasFiniteSupport A.fields a b ((d : ℤ) - 1)
    have h' := Function.HasFiniteSupport.comp h (g := fun x : V => ‖x‖ ^ 2) (by simp)
    have he (m : ℕ) : (m : ℤ) + d - 1 = d - 1 + m := by omega
    simpa only [Function.comp_def, physicalMode, he] using h' 
  have hg := normal_product_norms_hasFiniteSupport (A := A) a b d
  rw [← tsum_eq_finsum (L := SummationFilter.unconditional ℕ) hf,
    ← tsum_eq_finsum (L := SummationFilter.unconditional ℕ) hg]
  apply Summable.tsum_le_tsum_of_inj (fun m => m + (d - 1))
    (by intro x y h; dsimp at h; omega) (by intro i hi; positivity) _
    (summable_of_hasFiniteSupport hf) (summable_of_hasFiniteSupport hg)
  intro m
  have he : ((m + (d - 1) : ℕ) : ℤ) + 1 - d = m := by omega
  rw [he]
  exact le_add_of_nonneg_left (sq_nonneg _)

 

theorem normal_product_nonneg {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) (b : V) :
    0 ≤ (inner ℂ (mode A.fields (mode A.fields a (-1) a) (2 * (d : ℤ) - 1) b) b).re := by
  rw [U.normal_product_quadratic ha hq hh]
  exact finsum_nonneg (fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _))

 

theorem normalProductTrace_nonneg {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) (h : ℕ) :
    0 ≤ A.normalProductTrace ha h := by
  let := A.grade_finite h
  apply re_trace_nonneg_of_quadratic
  intro b
  change 0 ≤ (inner ℂ (A.normalProductOnGrade ha h b : V) (b : V)).re
  rw [A.normalProductOnGrade_apply]
  exact U.normal_product_nonneg ha hq hh b

 

theorem positive_column_le_grade_trace {a : V} {d : ℕ} (hd : 1 ≤ d)
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    {h : ℕ} {b : V} (hb : b ∈ A.grade h) (hbn : ‖b‖ = 1) :
    (∑ᶠ m : ℕ, ‖A.physicalMode a d m b‖ ^ 2) ≤ A.normalProductTrace ha h := by
  apply le_trans (U.positive_column hd ha hq hh b)
  let := A.grade_finite h
  have hpos (x : A.grade h) : 0 ≤ (inner ℂ (A.normalProductOnGrade ha h x) x).re := by
    change 0 ≤ (inner ℂ (A.normalProductOnGrade ha h x : V) (x : V)).re
    rw [A.normalProductOnGrade_apply]
    exact U.normal_product_nonneg ha hq hh x
  have hx := quadratic_le_re_trace (A.normalProductOnGrade ha h) hpos ⟨b, hb⟩ hbn
  change (inner ℂ (A.normalProductOnGrade ha h ⟨b, hb⟩ : V) b).re ≤ _ at hx
  rwa [A.normalProductOnGrade_apply] at hx

omit U in
 

theorem normalProductTrace_summable_of_onePoint (hconv : A.OrdinaryOnePointConvergence)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    Summable (fun h : ℕ => q ^ h * A.normalProductTrace ha h) := by
  have h := hconv (2 * d) _ (A.normalProduct_mem_grade ha) q hq hq1
  have hr := (Complex.hasSum_re h.hasSum).summable
  simpa only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, gradedTraceCoefficient,
    normalProductOnGrade, normalProductTrace] using hr

 

theorem positive_column_le_weighted_trace {a : V} {d : ℕ} (hd : 1 ≤ d)
    (ha : a ∈ A.grade d) (hqa : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    {q : ℝ} (hq : 0 < q)
    (hs : Summable (fun h : ℕ => q ^ h * A.normalProductTrace ha h))
    {h : ℕ} {b : V} (hb : b ∈ A.grade h) (hbn : ‖b‖ = 1) :
    (∑ᶠ m : ℕ, ‖A.physicalMode a d m b‖ ^ 2) ≤
      (∑' k : ℕ, q ^ k * A.normalProductTrace ha k) / q ^ h := by
  apply le_trans (U.positive_column_le_grade_trace hd ha hqa hh hb hbn)
  apply (le_div_iff₀ (pow_pos hq h)).mpr
  rw [mul_comm]
  exact hs.le_tsum h (fun k _ => mul_nonneg (pow_nonneg hq.le k)
    (U.normalProductTrace_nonneg ha hqa hh k))

 
theorem pct_mem_grade {d : ℕ} {a : V} (ha : a ∈ A.grade d) :
    U.pct a ∈ A.grade d := by
  apply A.mem_grade_of_energy
  rw [← U.pct_virasoro, A.virasoro_zero_on_grade ha]
  simp

 

def hermitianConjugation (d : ℕ) : V →ₛₗ[starRingEnd ℂ] V :=
  ((-1 : ℂ) ^ d) • U.pct

theorem hermitianConjugation_involutive (d : ℕ) :
    Function.Involutive (U.hermitianConjugation d) := by
  intro a
  simp only [hermitianConjugation, LinearMap.smul_apply, map_smulₛₗ,
    map_pow, map_neg, map_one, U.pct_involutive a, smul_smul, ← mul_pow]
  simp

 

theorem exists_hermitian_quasiPrimary_spanning (d : ℕ) :
    ∃ S : Finset V,
      (∀ a ∈ S, a ∈ A.grade d ∧ A.IsQuasiPrimary a ∧ U.IsHermitian d a) ∧
      (∀ a ∈ A.grade d, A.IsQuasiPrimary a → a ∈ Submodule.span ℂ (S : Set V)) := by
  classical
  let E := A.grade d ⊓ (A.virasoroMode 1).ker
  let J := U.hermitianConjugation d
  let H := {a : V | a ∈ E ∧ J a = a}
  have hJin (a : V) (ha : a ∈ E) : J a ∈ E := by
    refine ⟨(A.grade d).smul_mem _ (U.pct_mem_grade ha.1), ?_⟩
    change A.virasoroMode 1 (((-1 : ℂ)^d) • U.pct a) = 0
    rw [map_smul, ← U.pct_virasoro, (LinearMap.mem_ker.mp ha.2), map_zero, smul_zero]
  have hJ (a : V) : J (J a) = a := U.hermitianConjugation_involutive d a
  have hfix (a : V) (ha : a ∈ E) : a + J a ∈ H := by
    refine ⟨E.add_mem ha (hJin a ha), ?_⟩
    rw [map_add, hJ, add_comm]
  have hspan : E ≤ Submodule.span ℂ H := by
    intro a ha
    have hx := Submodule.subset_span (R := ℂ) (hfix a ha)
    have hy := Submodule.subset_span (R := ℂ) (hfix (Complex.I • a) (E.smul_mem _ ha))
    have he : a = (2 : ℂ)⁻¹ • (a + J a) +
        (-Complex.I / 2 : ℂ) • (Complex.I • a + J (Complex.I • a)) := by
      rw [map_smulₛₗ, show starRingEnd ℂ Complex.I = -Complex.I from Complex.conj_I]
      simp only [smul_add, smul_smul]
      have hI : (-Complex.I / 2 : ℂ) * Complex.I = (2 : ℂ)⁻¹ := by
        rw [div_mul_eq_mul_div, neg_mul, Complex.I_mul_I]
        norm_num
      rw [hI, mul_neg, hI]
      module
    rw [he]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hx) (Submodule.smul_mem _ _ hy)
  let := A.grade_finite d
  have : FiniteDimensional ℂ E := Submodule.finiteDimensional_of_le inf_le_left
  obtain ⟨T, hT⟩ := (Submodule.FG.of_finite (N := E))
  have hTspan : (T : Set V) ⊆ Submodule.span ℂ H := by
    intro a ha
    exact hspan (hT ▸ Submodule.subset_span ha)
  obtain ⟨S, hSH, hTS⟩ := Submodule.subset_span_finite_of_subset_span hTspan
  refine ⟨S, ?_, ?_⟩
  · intro a ha
    have h := hSH ha
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro a ha hqa
    have hle : E ≤ Submodule.span ℂ (S : Set V) := by
      rw [← hT]
      exact Submodule.span_le.mpr hTS
    exact hle ⟨ha, hqa⟩

 

theorem quasiPrimary_decomposition {d : ℕ} {a : V} (ha : a ∈ A.grade (d + 1)) :
    ∃ q ∈ A.grade (d + 1), A.IsQuasiPrimary q ∧
      ∃ b ∈ A.grade d, a = q + A.virasoroMode (-1) b := by
  let K := (A.grade d).map (A.virasoroMode (-1))
  let := A.grade_finite d
  have : FiniteDimensional ℂ K := Module.Finite.map _ _
  obtain ⟨y, hy, q, hq, hayq⟩ := K.exists_add_mem_mem_orthogonal a
  obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hy
  have hygrade := A.virasoro_mem_grade hb (-1) (k := d + 1) (by omega)
  have hqgrade : q ∈ A.grade (d + 1) := by
    have he : q = a - A.virasoroMode (-1) b := by rw [hayq]; abel
    rw [he]
    exact (A.grade (d + 1)).sub_mem ha hygrade
  have hLq : A.virasoroMode 1 q ∈ A.grade d :=
    A.virasoro_mem_grade hqgrade 1 (by omega)
  have hzero : A.virasoroMode 1 q = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    have hmem : A.virasoroMode (-1) (A.virasoroMode 1 q) ∈ K :=
      Submodule.mem_map.mpr ⟨A.virasoroMode 1 q, hLq, rfl⟩
    have h := (K.mem_orthogonal q).mp hq _ hmem
    simpa only [U.virasoro_adjoint, neg_neg, Int.reduceNeg] using h
  exact ⟨q, hqgrade, hzero, b, hb, hayq.trans (add_comm _ _)⟩

 

theorem grade_blockGrowth {B : ℕ → ℝ} (hB : ∀ N, 1 ≤ B N) (D : ℕ)
    (hsmall : ∀ d, 1 ≤ d → d ≤ D → ∀ a ∈ A.grade d, A.IsQuasiPrimary a →
      A.BlockGrowth B a d d)
    (hcut : ∀ d, D < d → A.grade d ≤ A.toVertexAlgebra.c2) :
    ∀ d, ∀ a ∈ A.grade d, A.BlockGrowth B a d d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro a ha
    by_cases hd0 : d = 0
    · subst d
      rw [A.grade_zero] at ha
      obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp ha
      exact A.blockGrowth_smul (A.vacuum_blockGrowth B) z
    by_cases hdD : d ≤ D
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0
      obtain ⟨q, hq, hqq, b, hb, hab⟩ := U.quasiPrimary_decomposition ha
      rw [hab, A.virasoro_neg_one_eq_translation]
      exact A.blockGrowth_add hB (hsmall _ (by omega) hdD q hq hqq)
        (A.blockGrowth_mono_weight hB (A.translation_blockGrowth hB (ih e (by omega) b hb))
          (by omega))
    · have hc : a ∈ A.homogeneousC2 d := by
        rw [A.homogeneousC2_eq]
        exact ⟨hcut d (by omega) ha, ha⟩
      exact A.homogeneousC2_le_blockGrowth hB d ih hc

 

theorem exists_generatorMajorant (hc : A.toVertexAlgebra.C2Cofinite) :
    ∃ D : ℕ, 2 ≤ D ∧ ∃ S : ℕ → Finset V,
      (∀ d, d = 0 ∨ D < d → S d = ∅) ∧
      (∀ d, ∀ a ∈ S d, 1 ≤ d ∧ d ≤ D ∧ a ∈ A.grade d ∧
        A.IsQuasiPrimary a ∧ U.IsHermitian d a) ∧
      ∀ w, ∀ a ∈ A.grade w, A.BlockGrowth (A.generatorMajorant D S) a w w := by
  classical
  obtain ⟨D, hD, hcut⟩ := A.exists_c2_weight_cutoff hc
  choose R hR hspan using U.exists_hermitian_quasiPrimary_spanning
  let S : ℕ → Finset V := fun d => if 1 ≤ d ∧ d ≤ D then R d else ∅
  have hS (d : ℕ) (a : V) (ha : a ∈ S d) :
      1 ≤ d ∧ d ≤ D ∧ a ∈ A.grade d ∧ A.IsQuasiPrimary a ∧ U.IsHermitian d a := by
    dsimp only [S] at ha
    split_ifs at ha with hd
    · exact ⟨hd.1, hd.2, hR d a ha⟩
    · simp at ha
  refine ⟨D, hD, S, ?_, hS, ?_⟩
  · intro d hd
    dsimp [S]
    rw [ite_eq_right]
    omega
  · apply U.grade_blockGrowth (A.one_le_generatorMajorant D S) D _ hcut
    intro d hd hdD a ha hq
    have he : S d = R d := by dsimp [S]; rw [ite_eq_left ⟨hd, hdD⟩]
    have hmem : a ∈ Submodule.span ℂ (S d : Set V) := by
      rw [he]
      exact hspan d a ha hq
    have hle : Submodule.span ℂ (S d : Set V) ≤
        A.blockGrowthSubmodule (A.generatorMajorant D S) (A.one_le_generatorMajorant D S) d d := by
      apply Submodule.span_le.mpr
      intro b hb
      exact A.generator_blockGrowth D S (by omega) hdD hb
    exact hle hmem

 

theorem generatorMajorant_polynomial (D : ℕ) (hD : 2 ≤ D) (S : ℕ → Finset V)
    (hS : ∀ d, ∀ a ∈ S d, 1 ≤ d ∧ d ≤ D ∧ a ∈ A.grade d ∧
      A.IsQuasiPrimary a ∧ U.IsHermitian d a)
    (H : ∀ w, ∀ a ∈ A.grade w, A.BlockGrowth (A.generatorMajorant D S) a w w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ N,
      A.generatorMajorant D S N ≤ C * (1 + (N : ℝ))^p := by
  classical
  let B := A.generatorMajorant D S
  have hB := A.one_le_generatorMajorant D S
  let G := (Finset.range (D + 1)).sigma S
  have HG (i : Σ _ : ℕ, V) (hi : i ∈ G) :
      1 ≤ i.1 ∧ i.1 ≤ D ∧ i.2 ∈ A.grade i.1 ∧
        A.IsQuasiPrimary i.2 ∧ U.IsHermitian i.1 i.2 :=
    hS i.1 i.2 (Finset.mem_sigma.mp hi).2
  have Hsq (i : Σ _ : ℕ, V) (hi : i ∈ G) :
      ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ N (hk : ℕ × ℕ), hk.1 ≤ N ∧ hk.2 ≤ N →
        ‖A.modeBlock i.2 i.1 hk.1 hk.2‖^2 ≤
          C * (1 + (N : ℝ))^p * B N^(2 * i.1 - 1) := by
    obtain ⟨hd, _, ha, hq, hh⟩ := HG i hi
    obtain ⟨C, hC, p, hp⟩ := U.modeBlock_norm_sq_bound hB ha hd hq hh
      (fun j hj => H _ _ (A.mode_mem_grade ha ha j (by omega)))
    exact ⟨C, hC, p, fun N hk hh => hp N hk.1 hk.2 hh.1 hh.2⟩
  obtain ⟨C, hC, p, hp⟩ := finite_weighted_poly_uniform hB G
    (fun (i : Σ _ : ℕ, V) (_ : ℕ) (hk : ℕ × ℕ) => ‖A.modeBlock i.2 i.1 hk.1 hk.2‖^2)
    (fun i => 2 * i.1 - 1) (fun N (hk : ℕ × ℕ) => hk.1 ≤ N ∧ hk.2 ≤ N) Hsq
  let J : ℝ := (G.card : ℝ) + 1
  have hJ : 1 ≤ J := by dsimp [J]; exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  refine ⟨J^(2 * D) * (C + 1), by positivity, 4 * D + p, ?_⟩
  intro N
  have hBN : 0 ≤ B N := zero_le_one.trans (hB N)
  have hBN' : 0 ≤ A.generatorMajorant D S N := hBN
  let s := G ×ˢ (Finset.range (N + 1) ×ˢ Finset.range (N + 1))
  let x : ((Σ _ : ℕ, V) × (ℕ × ℕ)) → ℝ :=
    fun i => ‖A.modeBlock i.1.2 i.1.1 i.2.1 i.2.2‖ ^ (i.1.1 : ℝ)⁻¹
  have hx (i) : 0 ≤ x i := by
    dsimp [x]
    exact Real.rpow_nonneg (norm_nonneg (A.modeBlock _ _ _ _)) _
  have hsum : 1 + ∑ i ∈ s, x i = B N := by
    simp only [s, x, G, B, generatorMajorant, Finset.sum_product, Finset.sum_sigma]
  let R := (C + 1) * (1 + (N : ℝ))^p
  have hN1 : 1 ≤ 1 + (N : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg N)
  have hR : 1 ≤ R := by
    dsimp [R]
    nlinarith [one_le_pow₀ hN1 (n := p)]
  have hstep (i) (hi : i ∈ s) : (x i)^(2 * D) ≤ R * (B N)^(2 * D - 1) := by
    obtain ⟨hiG, hhk⟩ := Finset.mem_product.mp hi
    obtain ⟨hh, hk⟩ := Finset.mem_product.mp hhk
    have hhN : i.2.1 ≤ N := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hh
    have hkN : i.2.2 ≤ N := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
    have hs := HG i.1 hiG
    have hroot : x i ≤ B N := A.root_modeBlock_le_generatorMajorant D S hs.2.1
      (Finset.mem_sigma.mp hiG).2 hhN hkN
    have hpow : (x i)^(2 * i.1.1) = ‖A.modeBlock i.1.2 i.1.1 i.2.1 i.2.2‖^2 := by
      rw [mul_comm 2 i.1.1, pow_mul]
      dsimp [x]
      rw [Real.rpow_inv_natCast_pow (norm_nonneg (A.modeBlock _ _ _ _)) (by omega)]
    have hsq := hp i.1 hiG N i.2 ⟨hhN, hkN⟩
    have hsq' : (x i)^(2 * i.1.1) ≤ R * (B N)^(2 * i.1.1 - 1) := by
      rw [hpow]
      apply hsq.trans
      dsimp [R]
      gcongr
      linarith
    have he : 2 * i.1.1 + (2 * D - 2 * i.1.1) = 2 * D := by omega
    have he' : (2 * i.1.1 - 1) + (2 * D - 2 * i.1.1) = 2 * D - 1 := by omega
    calc
      _ = (x i)^(2 * i.1.1) * (x i)^(2 * D - 2 * i.1.1) := by rw [← pow_add, he]
      _ ≤ (R * (B N)^(2 * i.1.1 - 1)) * (B N)^(2 * D - 2 * i.1.1) := by
        apply mul_le_mul hsq' (pow_le_pow_left₀ (hx i) hroot _) (pow_nonneg (hx i) _) (by positivity)
      _ = _ := by rw [mul_assoc, ← pow_add, he']
  have hcontract := finite_sum_power_contraction s x (2 * D) (by omega) R hR
    (fun i _ => hx i) (fun i hi => by rw [hsum]; exact hstep i hi)
  rw [hsum] at hcontract
  have hcard : (s.card : ℝ) + 1 ≤ J * (1 + (N : ℝ))^2 := by
    simp only [s, Finset.card_product, Finset.card_range, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one, J]
    nlinarith [Nat.cast_nonneg N (α := ℝ)]
  calc
    _ ≤ ((s.card : ℝ) + 1)^(2 * D) * R := hcontract
    _ ≤ (J * (1 + (N : ℝ))^2)^(2 * D) * R := by
      gcongr
    _ = _ := by
      dsimp [R]
      rw [mul_pow, ← pow_mul, ← mul_assoc, mul_right_comm _ _ (C + 1), mul_assoc,
        ← pow_add]
      congr 2
      omega

 

theorem energyBound_of_polynomial_blocks {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (H : ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ N,
      A.BlockControl a d N (C * (1 + (N : ℝ))^p)) : A.PolynomialEnergyBound a := by
  obtain ⟨C, hC, p, hp⟩ := H
  let K : ℝ := (C + 1) * ((d : ℝ) + 2)^p
  have hK : 0 < K := by dsimp [K]; positivity
  have hgrade (n : ℤ) (h : ℕ) (b : V) (hb : b ∈ A.grade h) :
      ‖mode A.fields a n b‖ ≤ K * (1 + |(n : ℝ)|)^p * (1 + (h : ℝ))^p * ‖b‖ := by
    by_cases hout : 0 ≤ (h : ℤ) + d - n - 1
    · let k := ((h : ℤ) + d - n - 1).toNat
      let N := h + d + 1 + n.natAbs
      have hk : (k : ℤ) = (h : ℤ) + d - n - 1 := Int.toNat_of_nonneg hout
      have hnabs : -n ≤ (n.natAbs : ℤ) := by simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -n))
      have hhN : h ≤ N := by dsimp [N]; omega
      have hkN : k ≤ N := by dsimp [N]; omega
      have hindex : (h : ℤ) - k + d - 1 = n := by omega
      have hblock := hp N h hhN k hkN b hb
      simp only [physicalMode, hindex] at hblock
      have habs : (n.natAbs : ℝ) = |(n : ℝ)| := by
        rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      have hN : 1 + (N : ℝ) ≤ ((d : ℝ) + 2) * (1 + |(n : ℝ)|) * (1 + (h : ℝ)) := by
        dsimp [N]
        push_cast
        rw [habs]
        have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
        have hh0 : 0 ≤ (h : ℝ) := Nat.cast_nonneg h
        have hn0 : 0 ≤ |(n : ℝ)| := abs_nonneg _
        nlinarith [mul_nonneg hd0 hn0, mul_nonneg hd0 hh0, mul_nonneg hn0 hh0,
          mul_nonneg (mul_nonneg hd0 hn0) hh0]
      apply hblock.trans
      have hc : C ≤ C + 1 := by linarith
      calc
        _ ≤ ((C + 1) * (((d : ℝ) + 2) * (1 + |(n : ℝ)|) * (1 + (h : ℝ)))^p) * ‖b‖ := by
          gcongr
        _ = _ := by dsimp [K]; simp only [mul_pow]; ring
    · rw [A.mode_eq_zero_of_negative_energy ha hb n (by omega), norm_zero]
      positivity
  refine ⟨K, hK, p, p, ?_⟩
  intro n b
  let L := K * (1 + |(n : ℝ)|)^p
  have hL : 0 ≤ L := by dsimp [L]; positivity
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mp
  change ‖mode A.fields a n b‖^2 ≤ (L * ‖(A.energyShift^p) b‖)^2
  rw [U.mode_norm_sq_eq_sum_grades ha]
  calc
    _ ≤ ∑ h ∈ A.gradeSupport b, (L * (1 + (h : ℝ))^p * ‖A.gradeComponent h b‖)^2 := by
      apply Finset.sum_le_sum
      intro h _
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      exact hgrade n h _ (A.gradeComponent_mem h b)
    _ = L^2 * ∑ h ∈ A.gradeSupport b, ((1 + (h : ℝ))^p * ‖A.gradeComponent h b‖)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ = _ := by rw [← U.energy_norm_sq_eq_sum_grades]; ring
end UnitaryStructure
end CFTTypeVOA
end StronglyRationalVOA

end

end OAI
