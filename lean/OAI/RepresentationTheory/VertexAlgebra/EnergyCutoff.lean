import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.MulLeftPow

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
def energyCutoff (N : ℕ) : Submodule ℂ V where
  carrier := {v | ∀ d, N < d → A.gradeComponent d v = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb d hd; simp only [map_add, ha d hd, hb d hd, add_zero]
  smul_mem' := by intro z a ha d hd; simp only [map_smul, ha d hd, smul_zero]

theorem grade_le_energyCutoff {d N : ℕ} (h : d ≤ N) : A.grade d ≤ A.energyCutoff N := by
  intro v hv e he
  exact A.gradeComponent_of_mem_ne (by omega) hv

theorem exists_energyCutoff (v : V) : ∃ N, v ∈ A.energyCutoff N := by
  classical
  refine ⟨(A.gradeSupport v).sup id, ?_⟩
  intro d hd
  have hn : d ∉ A.gradeSupport v := fun h => (not_le.mpr hd) (Finset.le_sup (f := id) h)
  have hz : A.gradingEquiv v d = 0 := DFinsupp.notMem_support_iff.mp hn
  exact congrArg Subtype.val hz

 
def cutoffProjection (N : ℕ) : Module.End ℂ V :=
  ∑ d ∈ Finset.range (N + 1), A.gradeComponent d

theorem cutoffProjection_apply (N : ℕ) (v : V) :
    A.cutoffProjection N v = ∑ d ∈ Finset.range (N + 1), A.gradeComponent d v := by
  simp [cutoffProjection]

theorem cutoffProjection_of_mem {N : ℕ} {v : V} (hv : v ∈ A.energyCutoff N) :
    A.cutoffProjection N v = v := by
  classical
  rw [cutoffProjection_apply]
  calc
    _ = ∑ d ∈ Finset.range (N + 1) ∪ A.gradeSupport v, A.gradeComponent d v := by
      apply Finset.sum_subset Finset.subset_union_left
      intro d _ hd
      exact hv d (by simp only [Finset.mem_range] at hd; omega)
    _ = ∑ d ∈ A.gradeSupport v, A.gradeComponent d v := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro d _ hd
      have hz : A.gradingEquiv v d = 0 := DFinsupp.notMem_support_iff.mp hd
      exact congrArg Subtype.val hz
    _ = v := A.sum_gradeComponents v

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

 
theorem energyShift_pow_norm_on_cutoff {N : ℕ} {v : V}
    (hv : v ∈ A.energyCutoff N) (r : ℕ) :
    ‖(A.energyShift ^ r) v‖ ≤ (1 + (N : ℝ))^r * ‖v‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [U.energy_norm_sq_eq_sum_grades, mul_pow, U.norm_sq_eq_sum_grades, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have hdN : d ≤ N := by
    by_contra h
    have hz := hv d (by omega)
    have hne : A.gradingEquiv v d ≠ 0 := DFinsupp.mem_support_iff.mp hd
    apply hne
    exact Subtype.ext hz
  have hdR : (d : ℝ) ≤ N := by exact_mod_cast hdN
  rw [mul_pow]
  gcongr

end UnitaryStructure

 

def mobiusGenerator : Module.End ℂ V :=
  (2 : ℂ)⁻¹ • (A.virasoroMode 1 - A.virasoroMode (-1))

theorem mobiusGenerator_mem_energyCutoff {N : ℕ} {v : V}
    (hv : v ∈ A.energyCutoff N) :
    A.mobiusGenerator v ∈ A.energyCutoff (N + 1) := by
  classical
  rw [← A.sum_gradeComponents v, map_sum]
  apply Submodule.sum_mem
  intro e he
  have heN : e ≤ N := by
    by_contra h
    have hz := hv e (by omega)
    exact (DFinsupp.mem_support_iff.mp he) (Subtype.ext hz)
  apply Submodule.smul_mem
  apply Submodule.sub_mem
  · by_cases he0 : e = 0
    · rw [A.virasoro_eq_zero_of_lt (A.gradeComponent_mem e v) 1 (by omega)]
      exact Submodule.zero_mem _
    · apply A.grade_le_energyCutoff (d := e - 1) (by omega)
      exact A.virasoro_mem_grade (A.gradeComponent_mem e v) 1 (by omega)
  · apply A.grade_le_energyCutoff (d := e + 1) (by omega)
    exact A.virasoro_mem_grade (A.gradeComponent_mem e v) (-1) (by omega)

theorem mobiusGenerator_pow_mem_energyCutoff {N : ℕ} {v : V}
    (hv : v ∈ A.energyCutoff N) (n : ℕ) :
    (A.mobiusGenerator ^ n) v ∈ A.energyCutoff (N + n) := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    simpa only [pow_succ', Module.End.mul_apply, Nat.add_assoc] using
      A.mobiusGenerator_mem_energyCutoff ih

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

 
theorem mobiusGenerator_skew (v w : V) :
    inner ℂ (A.mobiusGenerator v) w = - inner ℂ v (A.mobiusGenerator w) := by
  simp only [mobiusGenerator, LinearMap.smul_apply, LinearMap.sub_apply,
    inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
    U.virasoro_adjoint, neg_neg, map_inv₀, map_ofNat]
  ring

 
theorem mobiusGenerator_norm_cutoff {N : ℕ} {v : V}
    (hv : v ∈ A.energyCutoff N) :
    ‖A.mobiusGenerator v‖ ≤
      (8 * (1 + A.centralCharge.re)) * (1 + (N : ℝ)) * ‖v‖ := by
  have hc := U.centralCharge_nonneg.2
  have hpos := U.virasoro_linear_energy 1 v
  have hneg := U.virasoro_linear_energy (-1) v
  norm_num only [Int.cast_one, Int.cast_neg, abs_one, abs_neg, one_add_one_eq_two,
    Nat.reducePow] at hpos hneg
  have hE := U.energyShift_pow_norm_on_cutoff hv 1
  simp only [pow_one] at hE
  calc
    _ = (1 / 2 : ℝ) * ‖A.virasoroMode 1 v - A.virasoroMode (-1) v‖ := by
      simp [mobiusGenerator, norm_smul]
    _ ≤ 1 * (‖A.virasoroMode 1 v‖ + ‖A.virasoroMode (-1) v‖) :=
      mul_le_mul (by norm_num) (norm_sub_le _ _) (norm_nonneg _) (by norm_num)
    _ ≤ 8 * (1 + A.centralCharge.re) * ‖A.energyShift v‖ := by linarith
    _ ≤ _ := by
      calc
        _ ≤ 8 * (1 + A.centralCharge.re) * ((1 + (N : ℝ)) * ‖v‖) := by gcongr
        _ = _ := by ring

 
theorem mobiusGenerator_pow_norm {N : ℕ} {v : V} (hv : v ∈ A.energyCutoff N) (n : ℕ) :
    ‖(A.mobiusGenerator ^ n) v‖ ≤
      (8 * (1 + A.centralCharge.re))^n * ((N + 1).ascFactorial n : ℝ) * ‖v‖ := by
  have hc := U.centralCharge_nonneg.2
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    calc
      _ ≤ (8 * (1 + A.centralCharge.re)) * (1 + ((N + n : ℕ) : ℝ)) *
          ‖(A.mobiusGenerator ^ n) v‖ :=
        U.mobiusGenerator_norm_cutoff (A.mobiusGenerator_pow_mem_energyCutoff hv n)
      _ ≤ (8 * (1 + A.centralCharge.re)) * (1 + ((N + n : ℕ) : ℝ)) *
          ((8 * (1 + A.centralCharge.re))^n * ((N + 1).ascFactorial n : ℝ) * ‖v‖) := by
        gcongr
      _ = _ := by rw [Nat.ascFactorial_succ, pow_succ]; push_cast; ring

 

theorem summable_norm_mobiusEvolutionTerm {t : ℝ}
    (ht : 2 * |t| * (8 * (1 + A.centralCharge.re)) < 1) (v : V) :
    Summable (fun n => ‖LocalSkewFlow.skewExpTerm A.mobiusGenerator t n v‖) := by
  obtain ⟨N, hN⟩ := A.exists_energyCutoff v
  exact LocalSkewFlow.summable_norm_skewExpTerm _
    (by have hc := U.centralCharge_nonneg.2; positivity)
    (U.mobiusGenerator_pow_norm hN) ht

 

theorem mobiusEvolution_inner {t : ℝ}
    (ht : 2 * |t| * (8 * (1 + A.centralCharge.re)) < 1) (v w : V) :
    inner ℂ (LocalSkewFlow.skewExp A.mobiusGenerator t v)
      (LocalSkewFlow.skewExp A.mobiusGenerator t w) = inner ℂ v w :=
  LocalSkewFlow.inner_skewExp _ U.mobiusGenerator_skew t v w
    (U.summable_norm_mobiusEvolutionTerm ht v) (U.summable_norm_mobiusEvolutionTerm ht w)

 

def mobiusLocalIsometry (t : ℝ)
    (ht : 2 * |t| * (8 * (1 + A.centralCharge.re)) < 1) :
    V →ₗᵢ[ℂ] UniformSpace.Completion V where
  toFun := LocalSkewFlow.skewExp A.mobiusGenerator t
  map_add' v w := LocalSkewFlow.skewExp_add _ t v w
    (U.summable_norm_mobiusEvolutionTerm ht v) (U.summable_norm_mobiusEvolutionTerm ht w)
  map_smul' z v := LocalSkewFlow.skewExp_smul _ t z v
  norm_map' v := LocalSkewFlow.norm_skewExp _ U.mobiusGenerator_skew t v
    (U.summable_norm_mobiusEvolutionTerm ht v)

end UnitaryStructure

 
theorem virasoro_one_physical_commutator {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (m : ℤ) :
    A.virasoroMode 1 * A.physicalMode a d m - A.physicalMode a d m * A.virasoroMode 1 =
      ((d : ℂ) - 1 - m) • A.physicalMode a d (m + 1) := by
  ext v
  have h := A.mode_commutator_nat A.conformalVector a v 2 (m + (d : ℤ) - 1)
  have h0 : mode A.fields A.conformalVector 0 a = A.toVertexAlgebra.translation a :=
    by rw [A.conformal_translation]
  have h1 : mode A.fields A.conformalVector 1 a = (d : ℂ) • a :=
    A.virasoro_zero_on_grade ha
  have h2 : mode A.fields A.conformalVector 2 a = 0 := hq
  have ht := congrArg (fun f : Module.End ℂ V => f v)
    (A.translation_covariance a (m + d + 1))
  simp only [LinearMap.smul_apply] at ht
  norm_num [Finset.sum_range_succ, h0, h1, h2, mode_zero, mode_smul] at h
  rw [show (2 : ℤ) + (m + d - 1) = m + d + 1 by omega] at h
  rw [ht] at h
  simp only [show m + (d : ℤ) + 1 - 1 = m + d by omega] at h
  change A.virasoroMode 1 (A.physicalMode a d m v) -
    A.physicalMode a d m (A.virasoroMode 1 v) =
      ((d : ℂ) - 1 - m) • A.physicalMode a d (m + 1) v
  change mode A.fields A.conformalVector 2 (mode A.fields a (m + d - 1) v) -
    mode A.fields a (m + d - 1) (mode A.fields A.conformalVector 2 v) =
      ((d : ℂ) - 1 - m) • mode A.fields a (m + 1 + d - 1) v
  rw [show m + 1 + (d : ℤ) - 1 = m + d by omega, h]
  push_cast
  module

 
theorem virasoro_neg_one_physical_commutator (a : V) (d : ℕ) (m : ℤ) :
    A.virasoroMode (-1) * A.physicalMode a d m -
      A.physicalMode a d m * A.virasoroMode (-1) =
        (-((d : ℂ) - 1 + m)) • A.physicalMode a d (m - 1) := by
  ext v
  have h := A.mode_commutator_nat A.conformalVector a v 0 (m + (d : ℤ) - 1)
  have h0 : mode A.fields A.conformalVector 0 a = A.toVertexAlgebra.translation a :=
    by rw [A.conformal_translation]
  norm_num [Finset.sum_range_succ, h0] at h
  have ht := congrArg (fun f : Module.End ℂ V => f v)
    (A.translation_covariance a (m + d - 1))
  simp only [LinearMap.smul_apply] at ht
  change mode A.fields A.conformalVector 0 (mode A.fields a (m + d - 1) v) -
    mode A.fields a (m + d - 1) (mode A.fields A.conformalVector 0 v) =
      (-((d : ℂ) - 1 + m)) • mode A.fields a (m - 1 + d - 1) v
  rw [h, ht, show m + (d : ℤ) - 1 - 1 = m - 1 + d - 1 by omega]
  push_cast
  congr 1
  ring

 

theorem mobius_physical_commutator {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (m : ℤ) :
    A.mobiusGenerator * A.physicalMode a d m - A.physicalMode a d m * A.mobiusGenerator =
      (((d : ℂ) - 1 - m) / 2) • A.physicalMode a d (m + 1) +
      (((d : ℂ) - 1 + m) / 2) • A.physicalMode a d (m - 1) := by
  calc
    _ = (2 : ℂ)⁻¹ •
        ((A.virasoroMode 1 * A.physicalMode a d m - A.physicalMode a d m * A.virasoroMode 1) -
         (A.virasoroMode (-1) * A.physicalMode a d m - A.physicalMode a d m * A.virasoroMode (-1))) := by
      simp only [mobiusGenerator, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, smul_sub]
      abel
    _ = _ := by
      rw [A.virasoro_one_physical_commutator ha hq, A.virasoro_neg_one_physical_commutator]
      module

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

 

theorem physicalMode_polynomial_cutoff {a : V} (h : A.PolynomialEnergyBound a)
    (d : ℕ) (m : ℤ) : ∃ D : ℝ, 0 < D ∧ ∃ r : ℕ, ∀ {N : ℕ} {v : V},
    v ∈ A.energyCutoff N → ‖A.physicalMode a d m v‖ ≤ D * (1 + (N : ℝ))^r * ‖v‖ := by
  obtain ⟨C, hC, p, r, he⟩ := h
  refine ⟨C * (1 + |((m + (d : ℤ) - 1 : ℤ) : ℝ)|)^p, by positivity, r, ?_⟩
  intro N v hv
  apply (he (m + d - 1) v).trans
  have hg := U.energyShift_pow_norm_on_cutoff hv r
  calc
    _ ≤ C * (1 + |((m + (d : ℤ) - 1 : ℤ) : ℝ)|)^p * ((1 + (N : ℝ))^r * ‖v‖) := by
      gcongr
    _ = _ := by ring

 
theorem physicalMode_diagonal_zero {a v w : V} {d h : ℕ}
    (ha : a ∈ A.grade d) (hv : v ∈ A.grade h) (hw : w ∈ A.grade h)
    (m : ℤ) (hm : m ≠ 0) : inner ℂ v (A.physicalMode a d m w) = 0 := by
  by_cases hh : m ≤ (h : ℤ)
  · have hnat : 0 ≤ (h : ℤ) - m := by omega
    have hgrade : A.physicalMode a d m w ∈ A.grade ((h : ℤ) - m).toNat :=
      A.mode_mem_grade ha hw (m + d - 1) (by omega)
    exact U.grades_orthogonal (by omega) hv hgrade
  · change inner ℂ v (mode A.fields a (m + d - 1) w) = 0
    rw [A.mode_eq_zero_of_negative_energy ha hw (m + d - 1) (by omega), inner_zero_right]

end UnitaryStructure

 

theorem mobius_commutator_power {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (n : ℕ) :
    ((LocalSkewFlow.commutatorOperator (R := ℂ) A.mobiusGenerator)^n)
      (A.physicalMode a d 1) =
        MobiusCoefficients.representation (A.physicalMode a d) (MobiusCoefficients.coeff d n) := by
  let L := (LocalSkewFlow.commutatorOperator (R := ℂ) A.mobiusGenerator).restrictScalars ℝ
  have hL (m : ℤ) : L (A.physicalMode a d m) =
      (((d : ℝ) - 1 - m) / 2) • A.physicalMode a d (m + 1) +
      (((d : ℝ) - 1 + m) / 2) • A.physicalMode a d (m - 1) := by
    have he := A.mobius_physical_commutator ha hq m
    change LocalSkewFlow.commutatorOperator (R := ℂ) A.mobiusGenerator (A.physicalMode a d m) = _
    rw [LocalSkewFlow.commutatorOperator_apply, he]
    simp only [← Complex.coe_smul, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_add,
      Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_intCast, Complex.ofReal_ofNat]
  have h := MobiusCoefficients.representation_coeff (A.physicalMode a d) L d hL n
  convert h using 1
  clear h
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [pow_succ', Module.End.mul_apply]
      exact congrArg (LocalSkewFlow.commutatorOperator (R := ℂ) A.mobiusGenerator) ih

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

 
theorem mobius_commutator_diagonal {a v w : V} {d h : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a)
    (hv : v ∈ A.grade h) (hw : w ∈ A.grade h) (n : ℕ) :
    inner ℂ v ((((LocalSkewFlow.commutatorOperator (R := ℂ) A.mobiusGenerator)^n)
      (A.physicalMode a d 1)) w) =
       (MobiusCoefficients.coeff d n 0 : ℂ) * inner ℂ v (A.physicalMode a d 0 w) := by
  rw [A.mobius_commutator_power ha hq]
  let l : Module.End ℂ V →ₗ[ℝ] ℂ :=
    ((innerSL ℂ v).toLinearMap.comp (LinearMap.applyₗ w)).restrictScalars ℝ
  have hl (m : ℤ) (hm : m ≠ 0) : l (A.physicalMode a d m) = 0 :=
    U.physicalMode_diagonal_zero ha hv hw m hm
  have he := MobiusCoefficients.diagonal_representation (A.physicalMode a d) l hl
    (MobiusCoefficients.coeff d n)
  change inner ℂ v (((MobiusCoefficients.representation (A.physicalMode a d))
    (MobiusCoefficients.coeff d n)) w) =
      (MobiusCoefficients.coeff d n 0) • inner ℂ v (A.physicalMode a d 0 w) at he
  simpa only [Complex.real_smul] using he

end UnitaryStructure

theorem energyCutoff_mono : Monotone A.energyCutoff := by
  intro N M hNM v hv d hd
  exact hv d (by omega)

 
theorem mobiusTaylor_mem_energyCutoff {h : ℕ} {v : V}
    (hv : v ∈ A.energyCutoff h) (t : ℝ) (N : ℕ) :
    LocalSkewFlow.skewTaylor A.mobiusGenerator t N v ∈ A.energyCutoff (h + N) := by
  apply Submodule.sum_mem
  intro n hn
  apply Submodule.smul_mem
  exact A.energyCutoff_mono (by have h := Finset.mem_range.mp hn; omega)
    (A.mobiusGenerator_pow_mem_energyCutoff hv n)

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

 

theorem summable_norm_mobiusInserted {a : V} (hp : A.PolynomialEnergyBound a)
    (d : ℕ) (m : ℤ) {t : ℝ}
    (ht : 2 * |t| * (8 * (1 + A.centralCharge.re)) < 1) (v : V) :
    Summable (fun n => ‖LocalSkewFlow.insertedExpTerm A.mobiusGenerator
      (A.physicalMode a d m) t n v‖) := by
  obtain ⟨D, hD, r, hT⟩ := U.physicalMode_polynomial_cutoff hp d m
  obtain ⟨N, hN⟩ := A.exists_energyCutoff v
  apply LocalSkewFlow.summable_norm_insertedExpTerm _ _
    (by have hc := U.centralCharge_nonneg.2; positivity) hD.le
    (U.mobiusGenerator_pow_norm hN) (N := N) (r := r) _ ht
  intro n
  simpa only [Nat.cast_add, add_assoc] using
    hT (A.mobiusGenerator_pow_mem_energyCutoff hN n)

 

theorem mobius_diagonal_compression {a v w : V} {d h : ℕ}
    (hp : A.PolynomialEnergyBound a) (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a)
    (hv : v ∈ A.grade h) (hw : w ∈ A.grade h) {t : ℝ}
    (ht : 2 * |t| * (8 * (1 + A.centralCharge.re)) < 1) :
    inner ℂ (LocalSkewFlow.skewExp A.mobiusGenerator (-t) v)
      (LocalSkewFlow.insertedExp A.mobiusGenerator (A.physicalMode a d 1) (-t) w) =
        (MobiusCoefficients.mean d t : ℂ) * inner ℂ v (A.physicalMode a d 0 w) := by
  have ht' : 2 * |-t| * (8 * (1 + A.centralCharge.re)) < 1 := by simpa using ht
  rw [LocalSkewFlow.inner_skewExp_inserted _ _ U.mobiusGenerator_skew t v w
    (U.summable_norm_mobiusEvolutionTerm ht' v)
    (U.summable_norm_mobiusInserted hp d 1 ht' w)]
  simp_rw [U.mobius_commutator_diagonal ha hq hv hw]
  calc
    _ = ∑' n, ((t^n / (n.factorial : ℝ) * MobiusCoefficients.coeff d n 0 : ℝ) : ℂ) *
        inner ℂ v (A.physicalMode a d 0 w) := by
      apply tsum_congr
      intro n
      push_cast
      ring
    _ = _ := by rw [tsum_mul_right, ← Complex.ofReal_tsum]; rfl

 

theorem mobiusInserted_bound {a : V} (hp : A.PolynomialEnergyBound a) (d : ℕ) (m : ℤ)
    {t : ℝ} (ht : 4 * |t| * (8 * (1 + A.centralCharge.re)) < 1) :
    ∃ B E : ℝ, 0 ≤ B ∧ 0 ≤ E ∧ ∀ (F : ℕ → ℝ),
      (∀ N, ∀ v ∈ A.energyCutoff N, ‖A.physicalMode a d m v‖ ≤ F N * ‖v‖) →
      ∀ N, ∀ v ∈ A.energyCutoff N,
        ‖LocalSkewFlow.insertedExp A.mobiusGenerator (A.physicalMode a d m) t v‖ ≤
          (F (2 * N) * B + E) * ‖v‖ := by
  let C := 8 * (1 + A.centralCharge.re)
  have hC : 0 ≤ C := by dsimp [C]; have hc := U.centralCharge_nonneg.2; positivity
  obtain ⟨D, hD, r, hT⟩ := U.physicalMode_polynomial_cutoff hp d m
  let B := 1 + (1 - 4 * |t| * C)⁻¹
  let E := D * (2 : ℝ)^r * ∑' n : ℕ, (1 + (n : ℝ))^r * (4 * |t| * C)^n
  have hB : 0 ≤ B := by
    dsimp [B]
    have hh : 0 < 1 - 4 * |t| * C := by linarith
    positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    exact mul_nonneg (mul_nonneg hD.le (by positivity)) (tsum_nonneg (fun _ => by positivity))
  refine ⟨B, E, hB, hE, ?_⟩
  intro F hF N v hv
  have hF0 : 0 ≤ F (2 * N) := by
    have h := hF (2 * N) A.vacuum (A.grade_le_energyCutoff (d := 0) (by omega)
      (by rw [A.grade_zero]; exact Submodule.mem_span_singleton_self _))
    rw [U.vacuum_norm, mul_one] at h
    exact (norm_nonneg _).trans h
  have hq : 2 * |t| * C < 1 := by nlinarith [mul_nonneg (abs_nonneg t) hC]
  have hiter := U.mobiusGenerator_pow_norm hv
  have hTv (n : ℕ) : ‖A.physicalMode a d m ((A.mobiusGenerator^n) v)‖ ≤
      D * (1 + (N : ℝ) + n)^r * ‖(A.mobiusGenerator^n) v‖ := by
    simpa only [Nat.cast_add, add_assoc] using hT (A.mobiusGenerator_pow_mem_energyCutoff hv n)
  have hs := U.summable_norm_mobiusInserted hp d m hq v
  have he := LocalSkewFlow.apply_skewTaylor_add_tail A.mobiusGenerator (A.physicalMode a d m)
    (N := N) hs
  have hbnd := LocalSkewFlow.skewTaylor_norm_bound A.mobiusGenerator U.mobiusGenerator_skew hC hiter ht
  have htail := LocalSkewFlow.insertedExp_tail_norm_bound A.mobiusGenerator (A.physicalMode a d m)
    hC hD.le hiter hTv ht
  rw [← he]
  calc
    _ ≤ ‖(A.physicalMode a d m (LocalSkewFlow.skewTaylor A.mobiusGenerator t N v) : V)‖ +
        ‖∑' n, LocalSkewFlow.insertedExpTerm A.mobiusGenerator (A.physicalMode a d m) t (n + N) v‖ := by
      simpa only [UniformSpace.Completion.norm_coe] using norm_add_le
        ((A.physicalMode a d m (LocalSkewFlow.skewTaylor A.mobiusGenerator t N v) : V) : UniformSpace.Completion V)
        (∑' n, LocalSkewFlow.insertedExpTerm A.mobiusGenerator (A.physicalMode a d m) t (n + N) v)
    _ ≤ F (2 * N) * (B * ‖v‖) + E * ‖v‖ := by
      apply add_le_add _ htail
      apply (hF (2 * N) _ ?_).trans
      · exact mul_le_mul_of_nonneg_left hbnd hF0
      · simpa only [two_mul] using A.mobiusTaylor_mem_energyCutoff hv t N
    _ = _ := by ring

 

theorem zeroMode_transfer {a : V} {d : ℕ}
    (hp : A.PolynomialEnergyBound a) (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℕ → ℝ), (∀ N, 1 ≤ F N) →
      (∀ N, ∀ v ∈ A.energyCutoff N, ‖A.physicalMode a d 1 v‖ ≤ F N * ‖v‖) →
      ∀ h, ∀ w ∈ A.grade h, ‖A.physicalMode a d 0 w‖ ≤ C * F (2 * h) * ‖w‖ := by
  let L : ℝ := 8 * (1 + A.centralCharge.re)
  have hL : 0 < L := by dsimp [L]; have hc := U.centralCharge_nonneg.2; positivity
  let t : ℝ := (16 * L)⁻¹
  have ht : 0 < t := by dsimp [t]; positivity
  have h4 : 4 * |t| * L < 1 := by
    rw [abs_of_pos ht]
    dsimp [t]
    field_simp
    nlinarith
  have h4' : 4 * |-t| * L < 1 := by simpa using h4
  have h2 : 2 * |t| * L < 1 := by nlinarith [mul_nonneg (abs_nonneg t) hL.le]
  obtain ⟨B, E, hB, hE, hBE⟩ := U.mobiusInserted_bound hp d 1 h4'
  let c := MobiusCoefficients.mean d t
  have hc : 0 < c := MobiusCoefficients.mean_pos hd ht
  refine ⟨(1 + B + E) / c, div_pos (by positivity) hc, ?_⟩
  intro F hF hbound h w hw
  let v := A.physicalMode a d 0 w
  have hv : v ∈ A.grade h := A.mode_mem_grade ha hw ((0 : ℤ) + d - 1) (by omega)
  have hn := hBE F hbound h w (A.grade_le_energyCutoff le_rfl hw)
  have hi := U.mobius_diagonal_compression hp ha hq hv hw h2
  have he : ‖LocalSkewFlow.skewExp A.mobiusGenerator (-t) v‖ = ‖v‖ :=
    (U.mobiusLocalIsometry (-t) (by simpa using h2)).norm_map v
  have hh : c * ‖v‖^2 ≤ ‖v‖ * ((F (2 * h) * B + E) * ‖w‖) := by
    calc
      _ = ‖(c : ℂ) * inner ℂ v v‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc,
          inner_self_eq_norm_sq_to_K]
        simp
      _ = ‖inner ℂ (LocalSkewFlow.skewExp A.mobiusGenerator (-t) v)
        (LocalSkewFlow.insertedExp A.mobiusGenerator (A.physicalMode a d 1) (-t) w)‖ :=
          congrArg norm hi.symm
      _ ≤ ‖LocalSkewFlow.skewExp A.mobiusGenerator (-t) v‖ *
          ‖LocalSkewFlow.insertedExp A.mobiusGenerator (A.physicalMode a d 1) (-t) w‖ :=
            norm_inner_le_norm _ _
      _ ≤ _ := by rw [he]; exact mul_le_mul_of_nonneg_left hn (norm_nonneg _)
  by_cases hv0 : ‖v‖ = 0
  · change ‖v‖ ≤ _
    rw [hv0]
    have hFpos := (hF (2 * h)).trans_lt' (by norm_num : (0 : ℝ) < 1)
    positivity
  have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv0)
  have hvb : c * ‖v‖ ≤ (F (2 * h) * B + E) * ‖w‖ := by
    apply (mul_le_mul_iff_of_pos_left hvpos).mp
    nlinarith [hh]
  change ‖v‖ ≤ _
  apply (mul_le_mul_iff_of_pos_right hc).mp
  calc
    ‖v‖ * c ≤ (F (2 * h) * B + E) * ‖w‖ := by nlinarith [hvb]
    _ ≤ ((1 + B + E) * F (2 * h)) * ‖w‖ := by
      gcongr
      nlinarith [hF (2 * h)]
    _ = (((1 + B + E) / c * F (2 * h) * ‖w‖) * c) := by field_simp

end UnitaryStructure

end CFTTypeVOA

namespace SharpCombinatorics
end SharpCombinatorics
end StronglyRationalVOA

end

end OAI
