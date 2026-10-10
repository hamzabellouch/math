import OAI.Topology.EilenbergGanea.Regularization
import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

namespace OAI

noncomputable section

open Set Filter Topology
open scoped Quaternion ContDiff

open scoped Quaternion
namespace EilenbergGanea
abbrev SU2 := unitary ℍ

theorem quaternion_mem_unitary_iff (q : ℍ) : q ∈ unitary ℍ ↔ ‖q‖ = 1 := by
  rw [Unitary.mem_iff, Quaternion.star_mul_self, Quaternion.self_mul_star, and_self]
  constructor
  · intro h
    have he : Quaternion.normSq q = 1 := Quaternion.coe_inj.mp h
    rw [Quaternion.normSq_eq_norm_mul_self] at he
    nlinarith [norm_nonneg q]
  · intro h
    simp [Quaternion.normSq_eq_norm_mul_self, h]

instance su2_compactSpace : CompactSpace SU2 := by
  apply isCompact_iff_compactSpace.mp
  have hs : (unitary ℍ : Set ℍ) = Metric.sphere 0 1 := by
    ext q
    simp [quaternion_mem_unitary_iff]
  rw [hs]
  exact isCompact_sphere 0 1

def circleQuaternion : Circle →* SU2 where
  toFun z := ⟨Quaternion.ofComplex z, by
    rw [Unitary.mem_iff, Quaternion.star_mul_self, Quaternion.self_mul_star, and_self]
    have hz := Circle.normSq_coe z
    have he : Quaternion.normSq (Quaternion.ofComplex z) = 1 := by
      simpa [Quaternion.normSq_def', Complex.normSq_apply, sq] using hz
    rw [he]; rfl⟩
  map_one' := Subtype.ext (map_one Quaternion.ofComplex)
  map_mul' z w := Subtype.ext (map_mul Quaternion.ofComplex (z : ℂ) (w : ℂ))

@[simp] theorem circleQuaternion_coe (z : Circle) :
    ((circleQuaternion z : SU2) : ℍ) = (z : ℂ) := rfl

theorem circleQuaternion_injective : Function.Injective circleQuaternion := by
  intro z w h
  apply Subtype.ext
  apply Complex.ext
  · exact congrArg (fun q : ℍ => q.re) (congrArg Subtype.val h)
  · exact congrArg (fun q : ℍ => q.imI) (congrArg Subtype.val h)

theorem circleQuaternion_continuous : Continuous circleQuaternion := by
  apply Continuous.subtype_mk
  exact Quaternion.ofComplex.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val

def wordMap {m : ℕ} (w : Fin m → FreeGroup (Fin m)) (x : Fin m → SU2) : Fin m → SU2 :=
  fun i => FreeGroup.lift x (w i)

def exponentMatrix {m : ℕ} (w : Fin m → FreeGroup (Fin m)) : Matrix (Fin m) (Fin m) ℤ :=
  fun i j => Multiplicative.toAdd
    (FreeGroup.lift (fun k => Multiplicative.ofAdd (if j = k then (1 : ℤ) else 0)) (w i))

open Set Filter Topology
open scoped ContDiff

/-- Radial normalization is only used on nonzero quaternions. The harmless
value at zero makes it a total function without changing that domain. -/
def normalizeQuaternion (q : ℍ) : SU2 := by
  classical
  exact if h : q = 0 then 1 else
    ⟨‖q‖⁻¹ • q, (quaternion_mem_unitary_iff _).mpr (by
      simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr h))⟩

theorem normalizeQuaternion_coe_of_ne_zero {q : ℍ} (hq : q ≠ 0) :
    (normalizeQuaternion q : ℍ) = ‖q‖⁻¹ • q := by simp [normalizeQuaternion, hq]

theorem normalizeQuaternion_coe_contDiffAt {q : ℍ} (hq : q ≠ 0) :
    ContDiffAt ℝ ∞ (fun z => (normalizeQuaternion z : ℍ)) q := by
  have h : ContDiffAt ℝ ∞ (fun z : ℍ => ‖z‖⁻¹ • z) q :=
    ((contDiffAt_norm ℝ hq).inv (norm_ne_zero_iff.mpr hq)).smul contDiffAt_id
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hq] with z hz
  exact normalizeQuaternion_coe_of_ne_zero hz

theorem normalizeQuaternion_continuousAt {q : ℍ} (hq : q ≠ 0) :
    ContinuousAt normalizeQuaternion q := by
  exact tendsto_subtype_rng.mpr (normalizeQuaternion_coe_contDiffAt hq).continuousAt

@[simp] theorem normalizeQuaternion_unitary (q : SU2) : normalizeQuaternion (q : ℍ) = q := by
  have hqnorm : ‖(q : ℍ)‖ = 1 := (quaternion_mem_unitary_iff _).mp q.property
  have hq : (q : ℍ) ≠ 0 := by intro he; simp [he] at hqnorm
  apply Subtype.ext
  simp [normalizeQuaternion_coe_of_ne_zero hq, hqnorm]

/-- Smoothness of coefficient-free word evaluation follows directly by
induction, using quaternion conjugation for unitary inverses. -/
theorem freeGroup_lift_coe_contDiffAt {D ι : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] (w : FreeGroup ι)
    (a : D) (x : D → ι → SU2)
    (hx : ∀ i, ContDiffAt ℝ ∞ (fun z => (x z i : ℍ)) a) :
    ContDiffAt ℝ ∞ (fun z => ((FreeGroup.lift (x z) w : SU2) : ℍ)) a := by
  induction w using FreeGroup.induction_on with
  | one => simpa using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : D => (1 : ℍ)) a)
  | of i => simpa using hx i
  | inv_of i hi =>
      simp only [map_inv]
      change ContDiffAt ℝ ∞ (fun z => star ((FreeGroup.lift (x z) (FreeGroup.of i) : SU2) : ℍ)) a
      let L : ℍ →ₗ[ℝ] ℍ :=
        { toFun := star
          map_add' := star_add
          map_smul' := Quaternion.star_smul }
      exact L.toContinuousLinearMap.contDiff.contDiffAt.comp a hi
  | mul v w hv hw => simpa only [map_mul, Submonoid.coe_mul] using hv.mul hw

def radialWordMap {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (x : Fin m → ℍ) : Fin m → ℍ :=
  fun i => ‖x i‖ • ((wordMap w (fun j => normalizeQuaternion (x j)) i : SU2) : ℍ)

@[simp] theorem radialWordMap_norm {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (x : Fin m → ℍ) (i : Fin m) : ‖radialWordMap w x i‖ = ‖x i‖ := by
  have h : ‖((wordMap w (fun j => normalizeQuaternion (x j)) i : SU2) : ℍ)‖ = 1 :=
    (quaternion_mem_unitary_iff _).mp (wordMap w (fun j => normalizeQuaternion (x j)) i).property
  simp [radialWordMap, norm_smul, h]

theorem radialWordMap_contDiffAt {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (x : Fin m → ℍ) (hx : ∀ i, x i ≠ 0) : ContDiffAt ℝ ∞ (radialWordMap w) x := by
  apply contDiffAt_pi.mpr
  intro i
  exact ((contDiffAt_apply ℝ ℍ i x).norm ℝ (hx i)).smul
    (freeGroup_lift_coe_contDiffAt (w i) x (fun z j => normalizeQuaternion (z j))
      (fun j => (normalizeQuaternion_coe_contDiffAt (hx j)).comp (f := fun z : Fin m → ℍ => z j) x (contDiffAt_apply ℝ ℍ j x)))

theorem radialWordMap_eq_one_iff {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (x : Fin m → ℍ) : radialWordMap w x = 1 ↔
      (∀ i, ‖x i‖ = 1) ∧ wordMap w (fun j => normalizeQuaternion (x j)) = 1 := by
  constructor
  · intro h
    have hn (i : Fin m) : ‖x i‖ = 1 := by
      have he := congrArg (fun y : Fin m → ℍ => ‖y i‖) h
      simpa only [radialWordMap_norm, Pi.one_apply, norm_one] using he
    refine ⟨hn, ?_⟩
    funext i
    apply Subtype.ext
    have he := congrFun h i
    simpa [radialWordMap, hn] using he
  · rintro ⟨hn, hw⟩
    funext i
    simp [radialWordMap, hn, hw]


/-- A conjugation-invariant smooth cutoff, zero near coordinate hyperplanes
and one near the unit quaternion locus. -/
def radialCutoff {m : ℕ} (x : Fin m → ℍ) : ℝ :=
  ∏ i, Real.smoothTransition (4 * ‖x i‖ ^ 2 - 1)

def smoothRadialWordMap {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (x : Fin m → ℍ) : Fin m → ℍ := radialCutoff x • radialWordMap w x

theorem radialCutoff_contDiff {m : ℕ} : ContDiff ℝ ∞ (@radialCutoff m) := by
  apply contDiff_prod
  intro i _
  have hn : ContDiff ℝ ∞ (fun x : Fin m → ℍ => ‖x i‖ ^ 2) :=
    (contDiff_apply ℝ ℍ i).norm_sq ℝ
  exact Real.smoothTransition.contDiff.comp ((contDiff_const.mul hn).sub contDiff_const)

theorem radialCutoff_nonneg {m : ℕ} (x : Fin m → ℍ) : 0 ≤ radialCutoff x :=
  Finset.prod_nonneg (fun _ _ => Real.smoothTransition.nonneg _)

theorem radialCutoff_le_one {m : ℕ} (x : Fin m → ℍ) : radialCutoff x ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => Real.smoothTransition.nonneg _)
    (fun _ _ => Real.smoothTransition.le_one _)

theorem radialCutoff_eq_one {m : ℕ} (x : Fin m → ℍ) (hx : ∀ i, 1 ≤ ‖x i‖) :
    radialCutoff x = 1 := by
  apply Finset.prod_eq_one
  intro i _
  apply Real.smoothTransition.one_of_one_le
  nlinarith [hx i]

theorem radialCutoff_eventually_zero {m : ℕ} (x : Fin m → ℍ) (i : Fin m)
    (hi : x i = 0) : radialCutoff =ᶠ[𝓝 x] (fun _ => 0) := by
  have h : ∀ᶠ y in 𝓝 x, ‖y i‖ < (1 / 2 : ℝ) :=
    ((continuous_apply i).norm.continuousAt.eventually_lt_const (by simp [hi]))
  filter_upwards [h] with y hy
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply Real.smoothTransition.zero_of_nonpos
  nlinarith [norm_nonneg (y i)]

theorem radialCutoff_eventually_one {m : ℕ} (x : Fin m → ℍ)
    (hx : ∀ i, ‖x i‖ = 1) : radialCutoff =ᶠ[𝓝 x] (fun _ => 1) := by
  have h (i : Fin m) : ∀ᶠ y in 𝓝 x, (3 / 4 : ℝ) < ‖y i‖ :=
    ((continuous_apply i).norm.continuousAt.eventually_const_lt (by change (3 / 4 : ℝ) < ‖x i‖; rw [hx i]; norm_num))
  filter_upwards [Filter.eventually_all.mpr h] with y hy
  apply Finset.prod_eq_one
  intro i _
  apply Real.smoothTransition.one_of_one_le
  nlinarith [hy i]

theorem smoothRadialWordMap_contDiff {m : ℕ} (w : Fin m → FreeGroup (Fin m)) :
    ContDiff ℝ ∞ (smoothRadialWordMap w) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : ∀ i, x i ≠ 0
  · exact radialCutoff_contDiff.contDiffAt.smul (radialWordMap_contDiffAt w x hx)
  · push Not at hx
    obtain ⟨i, hi⟩ := hx
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Fin m → ℍ => (0 : Fin m → ℍ)) x).congr_of_eventuallyEq
    filter_upwards [radialCutoff_eventually_zero x i hi] with y hy
    simp [smoothRadialWordMap, hy]

theorem smoothRadialWordMap_eq_one_iff {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (x : Fin m → ℍ) : smoothRadialWordMap w x = 1 ↔ radialWordMap w x = 1 := by
  constructor
  · intro h
    have hn (i : Fin m) : radialCutoff x * ‖x i‖ = 1 := by
      have he := congrArg (fun y : Fin m → ℍ => ‖y i‖) h
      simpa only [smoothRadialWordMap, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (radialCutoff_nonneg x), radialWordMap_norm, Pi.one_apply, norm_one] using he
    have hlarge (i : Fin m) : 1 ≤ ‖x i‖ := by
      have hle := mul_le_mul_of_nonneg_right (radialCutoff_le_one x) (norm_nonneg (x i))
      rw [hn i, one_mul] at hle
      exact hle
    simpa only [smoothRadialWordMap, radialCutoff_eq_one x hlarge, one_smul] using h
  · intro h
    have hn := (radialWordMap_eq_one_iff w x).mp h
    simp only [smoothRadialWordMap, radialCutoff_eq_one x (fun i => (hn.1 i).ge), one_smul, h]

theorem smoothRadialWordMap_eventuallyEq {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (x : Fin m → ℍ) (hx : ∀ i, ‖x i‖ = 1) :
    smoothRadialWordMap w =ᶠ[𝓝 x] radialWordMap w := by
  filter_upwards [radialCutoff_eventually_one x hx] with y hy
  simp [smoothRadialWordMap, hy]

end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
variable {n : Type*} [Fintype n] [DecidableEq n]

def splitComplex : (n → ℂ) ≃ₗ[ℝ] ((n → ℝ) × (n → ℝ)) where
  toFun z := (fun i => (z i).re, fun i => (z i).im)
  invFun p i := (p.1 i : ℂ) + (p.2 i : ℂ) * Complex.I
  left_inv z := by funext i; exact Complex.re_add_im (z i)
  right_inv p := by ext i <;> simp
  map_add' a b := by ext i <;> simp
  map_smul' a b := by ext i <;> simp

def radialAngularLinear (B : Matrix n n ℝ) : (n → ℂ) →L[ℝ] (n → ℂ) :=
  ((splitComplex (n := n)).symm.toLinearMap.comp
    (((LinearMap.id : (n → ℝ) →ₗ[ℝ] (n → ℝ)).prodMap B.toLin').comp
      (splitComplex (n := n)).toLinearMap)).toContinuousLinearMap

@[simp] theorem radialAngularLinear_apply (B : Matrix n n ℝ) (z : n → ℂ) (i : n) :
    radialAngularLinear B z i = ((z i).re : ℂ) + (∑ j, B i j * (z j).im : ℝ) * Complex.I := rfl

theorem radialAngularLinear_det (B : Matrix n n ℝ) :
    (radialAngularLinear B).toLinearMap.det = B.det := by
  change LinearMap.det ((splitComplex (n := n)).symm.toLinearMap ∘ₗ
    ((LinearMap.id : (n → ℝ) →ₗ[ℝ] (n → ℝ)).prodMap B.toLin') ∘ₗ
    (splitComplex (n := n)).toLinearMap) = _
  have he := LinearMap.det_conj
    ((LinearMap.id : (n → ℝ) →ₗ[ℝ] (n → ℝ)).prodMap B.toLin')
    (splitComplex (n := n)).symm
  rw [LinearEquiv.symm_symm] at he
  rw [he, LinearMap.det_prodMap, LinearMap.det_id, one_mul, LinearMap.det_toLin']

def complexPolarChart (x z : n → ℂ) : n → ℂ := fun i => x i * Complex.exp (z i)

def complexRadialTorus (B : Matrix n n ℤ) (z : n → ℂ) : n → ℂ :=
  fun i => ‖z i‖ • ∏ j, (‖z j‖⁻¹ • z j) ^ B i j

theorem normalize_complex_mul_exp (x z : ℂ) (hx : ‖x‖ = 1) :
    ‖x * Complex.exp z‖⁻¹ • (x * Complex.exp z) =
      x * Complex.exp ((z.im : ℂ) * Complex.I) := by
  rw [norm_mul, hx, one_mul, Complex.norm_exp, Complex.real_smul, Complex.ofReal_inv]
  have he : Complex.exp z = (Real.exp z.re : ℂ) *
      Complex.exp ((z.im : ℂ) * Complex.I) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add, Complex.re_add_im]
  rw [he]
  have hn : (Real.exp z.re : ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero z.re
  field_simp

 theorem complexRadialTorus_chart (B : Matrix n n ℤ) (x : n → ℂ)
    (hx : ∀ i, ‖x i‖ = 1) (hroot : ∀ i, ∏ j, x j ^ B i j = 1) :
    complexRadialTorus B ∘ complexPolarChart x =
      fun z => fun i => Complex.exp (radialAngularLinear (B.map (Int.castRingHom ℝ)) z i) := by
  funext z i
  have hn (j : n) := normalize_complex_mul_exp (x j) (z j) (hx j)
  simp only [Function.comp_apply, complexRadialTorus, complexPolarChart]
  simp only [hn]
  simp only [mul_zpow, Finset.prod_mul_distrib,
    hroot, one_mul, norm_mul, hx, one_mul, Complex.norm_exp, radialAngularLinear_apply,
    ← Complex.exp_int_mul]
  rw [Complex.real_smul, Complex.ofReal_exp, ← Complex.exp_sum, ← Complex.exp_add]
  congr 1
  simp only [Matrix.map_apply, Int.coe_castRingHom, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_intCast]
  rw [Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring


/-- The real derivative of multiplication by a unit complex tuple has determinant one. -/
def complexDiagonal (x : n → ℂ) : (n → ℂ) →L[ℝ] (n → ℂ) :=
  ((Matrix.diagonal x).toLin').toContinuousLinearMap.restrictScalars ℝ

@[simp] theorem complexDiagonal_apply (x z : n → ℂ) (i : n) :
    complexDiagonal x z i = x i * z i := by simp [complexDiagonal, Matrix.toLin'_apply, Matrix.mulVec, Matrix.diagonal_apply, dotProduct]

theorem complexDiagonal_det (x : n → ℂ) (hx : ∀ i, ‖x i‖ = 1) :
    (complexDiagonal x).toLinearMap.det = 1 := by
  change (((Matrix.diagonal x).toLin').restrictScalars ℝ).det = _
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, LinearMap.det_toLin',
    Matrix.det_diagonal]
  rw [Complex.normSq_eq_norm_sq, norm_prod]
  simp [hx]

theorem complexPolarChart_hasFDerivAt (x : n → ℂ) :
    HasFDerivAt (complexPolarChart x) (complexDiagonal x) 0 := by
  apply hasFDerivAt_pi'.mpr
  intro i
  have h := ((ContinuousLinearMap.proj i : (n → ℂ) →L[ℝ] ℂ).hasFDerivAt
    (x := 0)).cexp.const_mul (x i)
  change HasFDerivAt (fun z : n → ℂ => x i * Complex.exp (z i)) _ (0 : n → ℂ)
  have he : (ContinuousLinearMap.proj i : (n → ℂ) →L[ℝ] ℂ).comp (complexDiagonal x) =
      x i • (ContinuousLinearMap.proj i : (n → ℂ) →L[ℝ] ℂ) := by
    ext z
    simp
  rw [he]
  simpa using h

theorem exp_radialAngularLinear_hasFDerivAt (B : Matrix n n ℝ) :
    HasFDerivAt (fun z i => Complex.exp (radialAngularLinear B z i))
      (radialAngularLinear B) 0 := by
  apply hasFDerivAt_pi'.mpr
  intro i
  simpa using (((ContinuousLinearMap.proj i : (n → ℂ) →L[ℝ] ℂ).comp
    (radialAngularLinear B)).hasFDerivAt (x := 0)).cexp

theorem complexRadialTorus_differentiableAt (B : Matrix n n ℤ) (x : n → ℂ)
    (hx : ∀ i, x i ≠ 0) : DifferentiableAt ℝ (complexRadialTorus B) x := by
  apply differentiableAt_pi.mpr
  intro i
  have hn (j : n) : DifferentiableAt ℝ (fun z : n → ℂ => ‖z j‖) x :=
    (differentiableAt_apply j x).norm ℝ (hx j)
  apply (hn i).smul
  have hp (j : n) : DifferentiableAt ℝ (fun z : n → ℂ => (‖z j‖⁻¹ • z j) ^ B i j) x := by
    have hne : ‖x j‖⁻¹ • x j ≠ 0 :=
      smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr (hx j))) (hx j)
    have hz : DifferentiableAt ℝ (fun z : ℂ => z ^ B i j) (‖x j‖⁻¹ • x j) :=
      ((differentiableAt_zpow (𝕜 := ℂ) (m := B i j)).mpr (Or.inl hne)).restrictScalars ℝ
    exact hz.comp x (((hn j).inv (norm_ne_zero_iff.mpr (hx j))).smul
      (differentiableAt_apply j x))
  exact (HasFDerivAt.finsetProd (fun j _ => (hp j).hasFDerivAt)).differentiableAt

/-- At every torus root, the radial extension has exactly determinant det B.
The extra radial coordinates contribute the identity, not an additional sign. -/
theorem complexRadialTorus_det (B : Matrix n n ℤ) (x : n → ℂ)
    (hx : ∀ i, ‖x i‖ = 1) (hroot : ∀ i, ∏ j, x j ^ B i j = 1) :
    (fderiv ℝ (complexRadialTorus B) x).det = (B.det : ℝ) := by
  have hne (i : n) : x i ≠ 0 := by intro h; simpa [h] using hx i
  have hd := (complexRadialTorus_differentiableAt B x hne).hasFDerivAt
  have hchart : complexPolarChart x 0 = x := by ext i; simp [complexPolarChart]
  have hc := (show HasFDerivAt (complexRadialTorus B) (fderiv ℝ (complexRadialTorus B) x)
      (complexPolarChart x 0) by rw [hchart]; exact hd).comp 0 (complexPolarChart_hasFDerivAt x)
  have he : (fderiv ℝ (complexRadialTorus B) x).comp (complexDiagonal x) =
      radialAngularLinear (B.map (Int.castRingHom ℝ)) := by
    apply hc.unique
    rw [complexRadialTorus_chart B x hx hroot]
    exact exp_radialAngularLinear_hasFDerivAt _
  have hdet := congrArg (fun L : (n → ℂ) →L[ℝ] (n → ℂ) => L.det) he
  change ((fderiv ℝ (complexRadialTorus B) x).toLinearMap.comp
    (complexDiagonal x).toLinearMap).det = (radialAngularLinear (B.map (Int.castRingHom ℝ))).toLinearMap.det at hdet
  rw [LinearMap.det_comp, complexDiagonal_det x hx,
    mul_one, radialAngularLinear_det] at hdet
  exact hdet.trans ((Int.castRingHom ℝ).map_det B).symm

end EilenbergGanea
namespace EilenbergGanea
section CommutativeWords
variable {n A : Type*} [Fintype n] [DecidableEq n] [CommGroup A]
def wordExponents {ι : Type*} [DecidableEq ι] (w : FreeGroup ι) (j : ι) : ℤ :=
  Multiplicative.toAdd
    (FreeGroup.lift (fun k => Multiplicative.ofAdd (if j = k then (1 : ℤ) else 0)) w)

@[simp] theorem wordExponents_one {ι : Type*} [DecidableEq ι] (j : ι) : wordExponents (1 : FreeGroup ι) j = 0 := by
  simp [wordExponents]

@[simp] theorem wordExponents_of {ι : Type*} [DecidableEq ι] (j k : ι) :
    wordExponents (FreeGroup.of k) j = if j = k then 1 else 0 := by
  simp [wordExponents]

@[simp] theorem wordExponents_inv {ι : Type*} [DecidableEq ι] (w : FreeGroup ι) (j : ι) :
    wordExponents w⁻¹ j = -wordExponents w j := by
  simp [wordExponents]

@[simp] theorem wordExponents_mul {ι : Type*} [DecidableEq ι] (w v : FreeGroup ι) (j : ι) :
    wordExponents (w * v) j = wordExponents w j + wordExponents v j := by
  simp [wordExponents]

theorem freeGroup_lift_commutative (x : n → A) (w : FreeGroup n) :
    FreeGroup.lift x w = ∏ j, x j ^ wordExponents w j := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of i => simp
  | inv_of i hi => simp [hi, Finset.prod_inv_distrib]
  | mul a b ha hb => simp [ha, hb, zpow_add, Finset.prod_mul_distrib]

end CommutativeWords
end EilenbergGanea
namespace EilenbergGanea
open Set Filter Topology
open scoped Quaternion ContDiff

def quaternionCoordinates : ℍ ≃ₗ[ℝ] ℂ × ℂ where
  toFun q := (⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩)
  invFun z := ⟨z.1.re, z.1.im, z.2.re, z.2.im⟩
  left_inv q := by cases q; rfl
  right_inv z := by rcases z with ⟨⟨a,b⟩,⟨c,d⟩⟩; rfl
  map_add' q r := by ext <;> rfl
  map_smul' r q := by apply Prod.ext <;> apply Complex.ext <;> simp

@[simp] theorem quaternionCoordinates_apply (q : ℍ) :
    quaternionCoordinates q = (⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩) := rfl

@[simp] theorem quaternionCoordinates_ofComplex (z : ℂ) :
    quaternionCoordinates (Quaternion.ofComplex z) = (z, 0) := by
  ext <;> rfl

@[simp] theorem norm_quaternion_ofComplex (z : ℂ) : ‖Quaternion.ofComplex z‖ = ‖z‖ := by
  have h : ‖Quaternion.ofComplex z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [sq, ← Quaternion.normSq_eq_norm_mul_self, ← Complex.normSq_eq_norm_sq]
    simp [Quaternion.normSq_def', Complex.normSq_apply, sq]
  nlinarith [norm_nonneg (Quaternion.ofComplex z), norm_nonneg z]

def quaternionTupleCoordinates {m : ℕ} :
    (Fin m → ℍ) ≃L[ℝ] ((Fin m → ℂ) × (Fin m → ℂ)) :=
  (show (Fin m → ℍ) ≃ₗ[ℝ] ((Fin m → ℂ) × (Fin m → ℂ)) from
    { toFun := fun q => (fun i => (quaternionCoordinates (q i)).1,
        fun i => (quaternionCoordinates (q i)).2)
      invFun := fun z i => quaternionCoordinates.symm (z.1 i, z.2 i)
      left_inv := by intro q; funext i; exact quaternionCoordinates.symm_apply_apply _
      right_inv := by intro z; ext i <;> simp
      map_add' := by intro q r; ext i <;> rfl
      map_smul' := by intro r q; ext i <;> simp [quaternionCoordinates] }).toContinuousLinearEquiv

@[simp] theorem quaternionTupleCoordinates_fixed {m : ℕ} (z : Fin m → ℂ) :
    quaternionTupleCoordinates (fun i => Quaternion.ofComplex (z i)) = (z, 0) := by
  apply Prod.ext
  · funext i; exact congrArg Prod.fst (quaternionCoordinates_ofComplex (z i))
  · funext i; exact congrArg Prod.snd (quaternionCoordinates_ofComplex (z i))

@[simp] theorem quaternionTupleCoordinates_symm_fixed {m : ℕ} (z : Fin m → ℂ) :
    quaternionTupleCoordinates.symm (z, 0) = fun i => Quaternion.ofComplex (z i) := by
  exact quaternionTupleCoordinates.injective (by rw [ContinuousLinearEquiv.apply_symm_apply, quaternionTupleCoordinates_fixed])

/-- Circle normalization chosen compatibly with quaternion normalization. -/
def normalizeCircle (z : ℂ) : Circle := by
  classical
  exact if hz : z = 0 then 1 else ⟨‖z‖⁻¹ • z, by apply mem_sphere_zero_iff_norm.mpr; simp [hz]⟩

theorem normalizeCircle_coe_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    (normalizeCircle z : ℂ) = ‖z‖⁻¹ • z := by simp [normalizeCircle, hz]

theorem normalizeQuaternion_ofComplex (z : ℂ) :
    normalizeQuaternion (Quaternion.ofComplex z) = circleQuaternion (normalizeCircle z) := by
  by_cases hz : z = 0
  · subst z
    simp [normalizeQuaternion, normalizeCircle]
  · have hq : Quaternion.ofComplex z ≠ 0 := by
      intro h
      have hh := congrArg quaternionCoordinates h
      apply hz
      have hz0 := congrArg Prod.fst hh
      change (quaternionCoordinates (Quaternion.ofComplex z)).1 = (quaternionCoordinates (Quaternion.ofComplex 0)).1 at hz0
      simpa only [quaternionCoordinates_ofComplex] using hz0
    apply Subtype.ext
    rw [normalizeQuaternion_coe_of_ne_zero hq, circleQuaternion_coe,
      normalizeCircle_coe_of_ne_zero hz, norm_quaternion_ofComplex]
    exact (map_smul Quaternion.ofComplex (‖z‖⁻¹) z).symm

theorem wordMap_circleQuaternion {m : ℕ} (w : Fin m → FreeGroup (Fin m)) (x : Fin m → Circle) :
    wordMap w (fun j => circleQuaternion (x j)) =
      fun i => circleQuaternion (∏ j, x j ^ exponentMatrix w i j) := by
  funext i
  have he : FreeGroup.lift (fun j => circleQuaternion (x j)) =
      circleQuaternion.comp (FreeGroup.lift x) := by
    apply FreeGroup.ext_hom
    intro j
    simp
  change FreeGroup.lift (fun j => circleQuaternion (x j)) (w i) = _
  rw [he, MonoidHom.comp_apply, freeGroup_lift_commutative]
  rfl

theorem radialWordMap_fixed {m : ℕ} (w : Fin m → FreeGroup (Fin m)) (z : Fin m → ℂ)
    (hz : ∀ i, z i ≠ 0) :
    radialWordMap w (fun i => Quaternion.ofComplex (z i)) =
      fun i => Quaternion.ofComplex (complexRadialTorus (exponentMatrix w) z i) := by
  funext i
  simp only [radialWordMap, normalizeQuaternion_ofComplex, wordMap_circleQuaternion,
    circleQuaternion_coe, complexRadialTorus, norm_quaternion_ofComplex]
  rw [map_smul]
  congr 1
  apply congrArg Quaternion.ofComplex
  change Circle.coeHom (∏ j, normalizeCircle (z j) ^ exponentMatrix w i j) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j _
  change (normalizeCircle (z j) : ℂ) ^ exponentMatrix w i j = _
  rw [normalizeCircle_coe_of_ne_zero (hz j)]

theorem quaternionCoordinates_conjComplex (c : ℂ) (q : ℍ) :
    quaternionCoordinates (Quaternion.ofComplex c * q * star (Quaternion.ofComplex c)) =
      ((Complex.normSq c : ℂ) * (quaternionCoordinates q).1,
        c ^ 2 * (quaternionCoordinates q).2) := by
  apply Prod.ext <;> apply Complex.ext <;>
    simp [quaternionCoordinates_apply, Complex.normSq_apply, pow_two] <;> ring

@[simp] theorem quaternionCoordinates_conjCircle (c : Circle) (q : ℍ) :
    quaternionCoordinates (Quaternion.ofComplex c * q * star (Quaternion.ofComplex c)) =
      ((quaternionCoordinates q).1, (c : ℂ) ^ 2 * (quaternionCoordinates q).2) := by
  simpa using quaternionCoordinates_conjComplex (c : ℂ) q

/-- Ambient conjugation, compatible with the group operation on unit quaternions. -/
def quaternionConjugate (a : SU2) (q : ℍ) : ℍ := (a : ℍ) * q * star (a : ℍ)

@[simp] theorem quaternionConjugate_norm (a : SU2) (q : ℍ) :
    ‖quaternionConjugate a q‖ = ‖q‖ := by
  have ha := (quaternion_mem_unitary_iff _).mp a.property
  simp [quaternionConjugate, ha]

@[simp] theorem quaternionConjugate_zero (a : SU2) : quaternionConjugate a 0 = 0 := by
  simp [quaternionConjugate]

@[simp] theorem quaternionConjugate_one (a : SU2) : quaternionConjugate a 1 = 1 := by
  simp [quaternionConjugate]

theorem quaternionConjugate_smul (a : SU2) (r : ℝ) (q : ℍ) :
    quaternionConjugate a (r • q) = r • quaternionConjugate a q := by
  simp only [quaternionConjugate, mul_smul_comm, smul_mul_assoc]

@[simp] theorem quaternionConjugate_coe (a q : SU2) :
    quaternionConjugate a (q : ℍ) = ((a * q * a⁻¹ : SU2) : ℍ) := rfl

theorem normalizeQuaternion_conjugate (a : SU2) (q : ℍ) :
    normalizeQuaternion (quaternionConjugate a q) = a * normalizeQuaternion q * a⁻¹ := by
  by_cases hq : q = 0
  · subst q; simp [normalizeQuaternion]
  · have hn : quaternionConjugate a q ≠ 0 := by
      intro hz
      have he := quaternionConjugate_norm a q
      rw [hz, norm_zero, eq_comm, norm_eq_zero] at he
      exact hq he
    apply Subtype.ext
    rw [normalizeQuaternion_coe_of_ne_zero hn, ← quaternionConjugate_coe,
      normalizeQuaternion_coe_of_ne_zero hq, quaternionConjugate_smul, quaternionConjugate_norm]

theorem wordMap_conjugation {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (a : SU2) (x : Fin m → SU2) :
    wordMap w (fun i => a * x i * a⁻¹) = fun i => a * wordMap w x i * a⁻¹ := by
  have he : FreeGroup.lift (fun i => a * x i * a⁻¹) =
      (MulAut.conj a).toMonoidHom.comp (FreeGroup.lift x) := by
    apply FreeGroup.ext_hom
    intro i
    simp
  funext i
  change FreeGroup.lift (fun i => a * x i * a⁻¹) (w i) = _
  rw [he]
  rfl

theorem radialWordMap_conjugation {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (a : SU2) (x : Fin m → ℍ) :
    radialWordMap w (fun i => quaternionConjugate a (x i)) =
      fun i => quaternionConjugate a (radialWordMap w x i) := by
  funext i
  simp only [radialWordMap, quaternionConjugate_norm, normalizeQuaternion_conjugate,
    wordMap_conjugation, quaternionConjugate_smul, quaternionConjugate_coe]

theorem smoothRadialWordMap_conjugation {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (a : SU2) (x : Fin m → ℍ) :
    smoothRadialWordMap w (fun i => quaternionConjugate a (x i)) =
      fun i => quaternionConjugate a (smoothRadialWordMap w x i) := by
  funext i
  simp only [smoothRadialWordMap, radialCutoff, quaternionConjugate_norm,
    Pi.smul_apply, radialWordMap_conjugation, quaternionConjugate_smul]

end EilenbergGanea


namespace EilenbergGanea

theorem complex_root_of_unity_norm {p : ℕ} (hp : p ≠ 0) (z : rootsOfUnity p ℂ) :
    ‖((z : ℂˣ) : ℂ)‖ = 1 := by
  have h := congrArg norm ((mem_rootsOfUnity' p (z : ℂˣ)).mp z.property)
  simpa only [norm_pow, norm_one, pow_eq_one_iff_of_nonneg (norm_nonneg _) hp] using h

theorem rootsOfUnity_isPGroup {p : ℕ} [Fact p.Prime] : IsPGroup p (rootsOfUnity p ℂ) := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [isPGroup_iff_card_dvd_pow, Complex.card_rootsOfUnity]
  exact ⟨1, by simp⟩

theorem rootsOfUnity_exists_nonreal {p : ℕ} (hp : 2 < p) :
    ∃ z : rootsOfUnity p ℂ, (((z : ℂˣ) : ℂ)).im ≠ 0 := by
  have hp0 : p ≠ 0 := by omega
  let ζ := Complex.exp (2 * Real.pi * Complex.I / p)
  have hζ : IsPrimitiveRoot ζ p := Complex.isPrimitiveRoot_exp p hp0
  let u : ℂˣ := Units.mk0 ζ (Complex.exp_ne_zero _)
  let z : rootsOfUnity p ℂ := ⟨u, (mem_rootsOfUnity' p u).mpr hζ.pow_eq_one⟩
  refine ⟨z, ?_⟩
  intro him
  change ζ.im = 0 at him
  have hn : ‖ζ‖ = 1 := complex_root_of_unity_norm hp0 z
  have hs : ζ.re ^ 2 = 1 := by
    have hh := Complex.normSq_eq_norm_sq ζ
    simp only [Complex.normSq_apply, him, mul_zero, add_zero, hn, one_pow] at hh
    nlinarith
  have hpow : ζ ^ 2 = 1 := by
    apply Complex.ext <;> simp [pow_two, him]
    nlinarith
  have hd := hζ.dvd_of_pow_eq_one 2 hpow
  have ht := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

theorem circle_exists_square_root (z : ℂ) (hz : ‖z‖ = 1) :
    ∃ c : Circle, (c : ℂ) ^ 2 = z := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq z (by decide : 0 < 2)
  have hn : ‖c‖ = 1 := by
    have hh := congrArg norm hc
    rw [norm_pow, hz] at hh
    nlinarith [norm_nonneg c]
  exact ⟨⟨c, mem_sphere_zero_iff_norm.mpr hn⟩, hc⟩

end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
open scoped Quaternion ContDiff

def splitWordMap {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (q : (Fin m → ℂ) × (Fin m → ℂ)) : (Fin m → ℂ) × (Fin m → ℂ) :=
  quaternionTupleCoordinates (smoothRadialWordMap w (quaternionTupleCoordinates.symm q)) - (1, 0)

theorem splitWordMap_contDiff {m : ℕ} (w : Fin m → FreeGroup (Fin m)) :
    ContDiff ℝ ∞ (splitWordMap w) :=
  (quaternionTupleCoordinates.contDiff.comp ((smoothRadialWordMap_contDiff w).comp
    quaternionTupleCoordinates.symm.contDiff)).sub contDiff_const

theorem quaternionTupleCoordinates_conjCircle {m : ℕ} (c : Circle) (q : Fin m → ℍ) :
    quaternionTupleCoordinates (fun i => quaternionConjugate (circleQuaternion c) (q i)) =
      ((quaternionTupleCoordinates q).1, (c : ℂ) ^ 2 • (quaternionTupleCoordinates q).2) := by
  apply Prod.ext
  · funext i
    change (quaternionCoordinates (Quaternion.ofComplex c * q i * star (Quaternion.ofComplex c))).1 = _
    have hh := congrArg Prod.fst (quaternionCoordinates_conjCircle c (q i))
    exact hh
  · funext i
    change (quaternionCoordinates (Quaternion.ofComplex c * q i * star (Quaternion.ofComplex c))).2 = _
    have hh := congrArg Prod.snd (quaternionCoordinates_conjCircle c (q i))
    exact hh

theorem splitWordMap_rotation {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (z : ℂ) (hz : ‖z‖ = 1) (q : (Fin m → ℂ) × (Fin m → ℂ)) :
    splitWordMap w (q.1, z • q.2) = ((splitWordMap w q).1, z • (splitWordMap w q).2) := by
  obtain ⟨c, hc⟩ := circle_exists_square_root z hz
  let x := quaternionTupleCoordinates.symm q
  have hx : quaternionTupleCoordinates x = q := quaternionTupleCoordinates.apply_symm_apply q
  have heq : (q.1, z • q.2) = quaternionTupleCoordinates
      (fun i => quaternionConjugate (circleQuaternion c) (x i)) := by
    rw [quaternionTupleCoordinates_conjCircle, hc, hx]
  have hh := congrArg (fun v : Fin m → ℍ => quaternionTupleCoordinates v)
    (smoothRadialWordMap_conjugation w (circleQuaternion c) x)
  rw [quaternionTupleCoordinates_conjCircle, hc] at hh
  have heq' : quaternionTupleCoordinates.symm (q.1, z • q.2) =
      fun i => quaternionConjugate (circleQuaternion c) (x i) := by
    rw [heq, ContinuousLinearEquiv.symm_apply_apply]
  unfold splitWordMap
  rw [heq', hh]
  change (_, z • _) - (1, 0) = ((quaternionTupleCoordinates (smoothRadialWordMap w x) - (1, 0)).1,
    z • (quaternionTupleCoordinates (smoothRadialWordMap w x) - (1, 0)).2)
  simp

theorem splitWordMap_fixed_eventually {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (x : Fin m → ℂ) (hx : ∀ i, ‖x i‖ = 1) :
    (fun z => (splitWordMap w (z, 0)).1) =ᶠ[𝓝 x]
      (fun z => complexRadialTorus (exponentMatrix w) z - 1) := by
  have hne (i : Fin m) : x i ≠ 0 := by intro h; simpa [h] using hx i
  have hz : ∀ᶠ z in 𝓝 x, ∀ i, z i ≠ 0 := Filter.eventually_all.mpr
    (fun i => (continuous_apply i).continuousAt.eventually_ne (hne i))
  have hcont : Continuous (fun z : Fin m → ℂ => fun i => Quaternion.ofComplex (z i)) :=
    continuous_pi (fun i => Quaternion.ofComplex.toLinearMap.continuous_of_finiteDimensional.comp
      (continuous_apply i))
  have he := (smoothRadialWordMap_eventuallyEq w (fun i => Quaternion.ofComplex (x i))
    (fun i => (norm_quaternion_ofComplex _).trans (hx i))).comp_tendsto hcont.continuousAt
  filter_upwards [hz, he] with z hz he
  change smoothRadialWordMap w (fun i => Quaternion.ofComplex (z i)) =
    radialWordMap w (fun i => Quaternion.ofComplex (z i)) at he
  simp only [splitWordMap, quaternionTupleCoordinates_symm_fixed]
  rw [he, radialWordMap_fixed w z hz, quaternionTupleCoordinates_fixed]
  rfl

theorem splitWordMap_fixed_det {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (x : Fin m → ℂ) (hx : ∀ i, ‖x i‖ = 1)
    (hr : ∀ i, ∏ j, x j ^ exponentMatrix w i j = 1) :
    (fderiv ℝ (fun z => (splitWordMap w (z, 0)).1) x).det =
      ((exponentMatrix w).det : ℝ) := by
  rw [(splitWordMap_fixed_eventually w x hx).fderiv_eq (𝕜 := ℝ)]
  have hne (i : Fin m) : x i ≠ 0 := by intro h; simpa [h] using hx i
  rw [((complexRadialTorus_differentiableAt (exponentMatrix w) x hne).hasFDerivAt.sub_const 1).fderiv]
  exact complexRadialTorus_det (exponentMatrix w) x hx hr

end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
open scoped Quaternion

theorem splitWordMap_zero_iff {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (q : (Fin m → ℂ) × (Fin m → ℂ)) :
    splitWordMap w q = 0 ↔
      smoothRadialWordMap w (quaternionTupleCoordinates.symm q) = 1 := by
  unfold splitWordMap
  rw [sub_eq_zero]
  have he : quaternionTupleCoordinates (1 : Fin m → ℍ) = (1, 0) := by
    change quaternionTupleCoordinates (fun i : Fin m => Quaternion.ofComplex (1 : ℂ)) = _
    exact quaternionTupleCoordinates_fixed 1
  rw [← he]
  exact quaternionTupleCoordinates.injective.eq_iff

theorem splitWordMap_fixed_zero_iff {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (z : Fin m → ℂ) : splitWordMap w (z, 0) = 0 ↔
      (∀ i, ‖z i‖ = 1) ∧ (∀ i, ∏ j, z j ^ exponentMatrix w i j = 1) := by
  rw [splitWordMap_zero_iff, quaternionTupleCoordinates_symm_fixed,
    smoothRadialWordMap_eq_one_iff]
  constructor
  · intro h
    have hn : ∀ i, ‖z i‖ = 1 := fun i => (norm_quaternion_ofComplex (z i)).symm.trans
      (((radialWordMap_eq_one_iff w _).mp h).1 i)
    have hz (i : Fin m) : z i ≠ 0 := by intro h; simpa [h] using hn i
    rw [radialWordMap_fixed w z hz] at h
    refine ⟨hn, fun i => ?_⟩
    have hh := congrArg (fun v : Fin m → ℍ => (quaternionCoordinates (v i)).1) h
    change (quaternionCoordinates (Quaternion.ofComplex _)).1 = (1 : ℂ) at hh
    simpa only [quaternionCoordinates_ofComplex, complexRadialTorus, hn, inv_one, one_smul] using hh
  · rintro ⟨hn, hr⟩
    have hz (i : Fin m) : z i ≠ 0 := by intro h; simpa [h] using hn i
    rw [radialWordMap_fixed w z hz]
    funext i
    simp [complexRadialTorus, hn, hr]

@[simp] theorem splitWordMap_fixed_one {m : ℕ} (w : Fin m → FreeGroup (Fin m)) :
    splitWordMap w (1, 0) = 0 := by
  rw [splitWordMap_fixed_zero_iff]
  simp

end EilenbergGanea

namespace EilenbergGanea
open Set
section Torus
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Type*} [CommGroup A]
theorem zpow_finite_sum {ι : Type*} (a : A) (s : Finset ι) (e : ι → ℤ) :
    a ^ (∑ i ∈ s, e i) = ∏ i ∈ s, a ^ e i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, zpow_add]

def torusMap (B : Matrix n n ℤ) (x : n → A) : n → A :=
  fun i => ∏ j, x j ^ B i j

omit [DecidableEq n] in
theorem torusMap_comp (B C : Matrix n n ℤ) (x : n → A) :
    torusMap B (torusMap C x) = torusMap (B * C) x := by
  funext i
  simp only [torusMap, Matrix.mul_apply, ← Finset.prod_zpow, zpow_finite_sum, ← zpow_mul]
  rw [Finset.prod_comm]
  congr 1
  funext j
  congr 1
  funext k
  rw [Int.mul_comm]

theorem torusMap_det_one (B : Matrix n n ℤ) (x : n → A) :
    torusMap (B.det • (1 : Matrix n n ℤ)) x = fun i => x i ^ B.det := by
  funext i
  simp [torusMap, Matrix.one_apply]

theorem torusMap_kernel_pow_det (B : Matrix n n ℤ) (x : n → A)
    (hx : torusMap B x = 1) (i : n) : x i ^ B.det = 1 := by
  have he := congrArg (fun y => torusMap B.adjugate y i) hx
  rw [torusMap_comp, Matrix.adjugate_mul, torusMap_det_one] at he
  simpa [torusMap] using he

theorem circle_finite_pow_roots {d : ℤ} (hd : d ≠ 0) :
    {z : Circle | z ^ d = 1}.Finite := by
  have hr := Polynomial.finite_setOfPred_isRoot
    (Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hd)) (1 : ℂ))
  apply Set.Finite.of_injOn (f := fun z : Circle => (z : ℂ)) _
    Subtype.val_injective.injOn hr
  intro z hz
  have hp : z ^ d.natAbs = 1 := pow_natAbs_eq_one.mpr hz
  have he : (z : ℂ) ^ d.natAbs = 1 := by
    simpa using congrArg (fun t : Circle => (t : ℂ)) hp
  simpa [Polynomial.IsRoot.def] using sub_eq_zero.mpr he

theorem torusMap_finite_kernel (B : Matrix n n ℤ) (hB : B.det ≠ 0) :
    {x : n → Circle | torusMap B x = 1}.Finite := by
  apply Set.Finite.subset (Set.Finite.pi (fun _ : n => circle_finite_pow_roots hB))
  intro x hx i _
  exact torusMap_kernel_pow_det B x hx i

end Torus
end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology

theorem splitWordMap_fixed_finite {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (hB : (exponentMatrix w).det ≠ 0) :
    {z : Fin m → ℂ | splitWordMap w (z, 0) = 0}.Finite := by
  classical
  let e : (Fin m → Circle) → (Fin m → ℂ) := fun x i => (x i : ℂ)
  have hf := (torusMap_finite_kernel (exponentMatrix w) hB).image e
  apply hf.subset
  intro z hz
  obtain ⟨hn, hr⟩ := (splitWordMap_fixed_zero_iff w z).mp hz
  let x : Fin m → Circle := fun i => ⟨z i, mem_sphere_zero_iff_norm.mpr (hn i)⟩
  refine ⟨x, ?_, rfl⟩
  funext i
  apply Subtype.ext
  change Circle.coeHom (∏ j, x j ^ exponentMatrix w i j) = (1 : ℂ)
  rw [map_prod]
  simp only [map_zpow]
  exact hr i

end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
open scoped ContDiff

/-- The signed-root noncancellation for the actual ambient quaternion word
map, with no regularity assumed of the original word map. -/
theorem word_exists_regularization_nonzero_count {m : ℕ}
    (w : Fin m → FreeGroup (Fin m)) (hB : (exponentMatrix w).det ≠ 0)
    (K : Set ((Fin m → ℂ) × (Fin m → ℂ))) (hK : IsCompact K)
    (hKi : ∀ z : ℂ, ‖z‖ = 1 → ∀ q ∈ K, (q.1, z • q.2) ∈ K)
    (h1 : (1, 0) ∈ K)
    (L : Set ((Fin m → ℂ) × (Fin m → ℂ))) (hL : IsCompact L) (hKL : K ⊆ L)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ((Fin m → ℂ) × (Fin m → ℂ)) → ((Fin m → ℂ) × (Fin m → ℂ)),
      ContDiff ℝ ∞ g ∧ (∀ q ∈ L, ‖g q - splitWordMap w q‖ < ε) ∧
      ∃ s : Finset ((Fin m → ℂ) × (Fin m → ℂ)),
        (∀ q, q ∈ s ↔ q ∈ K ∧ g q = 0) ∧
        (∀ q ∈ s, (fderiv ℝ g q).det ≠ 0) ∧
        (∑ q ∈ s, (if 0 < (fderiv ℝ g q).det then 1 else -1 : ℝ)) ≠ 0 := by
  classical
  let S := (splitWordMap_fixed_finite w hB).toFinset
  have hS (z) : z ∈ S ↔ splitWordMap w (z, 0) = 0 := (splitWordMap_fixed_finite w hB).mem_toFinset
  obtain ⟨p, hpbound, hp⟩ := Nat.exists_infinite_primes (S.card + 3)
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Fintype (rootsOfUnity p ℂ) := Fintype.ofFinite _
  obtain ⟨a₀, ha₀⟩ := rootsOfUnity_exists_nonreal (p := p) (by omega)
  let χ : rootsOfUnity p ℂ →* ℂˣ := (rootsOfUnity p ℂ).subtype
  apply exists_regularization_nonzero_count (rootsOfUnity_isPGroup (p := p)) χ
    Subtype.val_injective a₀ ha₀ (splitWordMap w) (splitWordMap_contDiff w)
    (fun a q => splitWordMap_rotation w (χ a : ℂ) (complex_root_of_unity_norm hp.ne_zero a) q)
    K hK (fun a q hq => hKi (χ a : ℂ) (complex_root_of_unity_norm hp.ne_zero a) q hq)
    L hL hKL S (fun z _ hz => (hS z).mpr hz) ⟨1, h1, splitWordMap_fixed_one w⟩ (by omega)
    ((exponentMatrix w).det : ℝ) (by exact_mod_cast hB) _ ε hε
  intro z hz
  obtain ⟨hn, hr⟩ := (splitWordMap_fixed_zero_iff w z).mp ((hS z).mp hz)
  exact splitWordMap_fixed_det w z hn hr

end EilenbergGanea

end

end OAI
