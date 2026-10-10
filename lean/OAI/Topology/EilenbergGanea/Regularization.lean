import Mathlib.Tactic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FiniteDimensional
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.RingTheory.Complex
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.MeasureTheory.Function.Jacobian

namespace OAI

noncomputable section

open Set Filter Topology

/-! Localized regularization for finite SU(2) systems. -/
namespace EilenbergGanea
section ComplexCentralizer
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
  [IsScalarTower ℝ ℂ V]

theorem complex_smul_decompose (z : ℂ) (x : V) :
    z • x = z.re • x + z.im • (Complex.I • x) := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [add_smul, mul_smul]
  change (algebraMap ℝ ℂ z.re) • x +
    (algebraMap ℝ ℂ z.im) • (Complex.I • x) = _
  simp only [IsScalarTower.algebraMap_smul]

/-- Commuting with a non-real scalar forces a real-linear map to be complex-linear. -/
theorem realLinear_map_complex_smul (f : V →ₗ[ℝ] V) (z : ℂ) (hz : z.im ≠ 0)
    (hf : ∀ x, f (z • x) = z • f x) (w : ℂ) (x : V) :
    f (w • x) = w • f x := by
  have hI (y : V) : f (Complex.I • y) = Complex.I • f y := by
    have he := hf y
    rw [complex_smul_decompose z y, complex_smul_decompose z (f y),
      map_add, map_smul, map_smul] at he
    exact smul_right_injective V hz (add_left_cancel he)
  rw [complex_smul_decompose w x, complex_smul_decompose w (f x),
    map_add, map_smul, map_smul, hI]

theorem complexLinear_of_commutes_nonreal (N : V →ₗ[ℝ] V) (z : ℂ) (hz : z.im ≠ 0)
    (h : ∀ v, N (z • v) = z • N v) :
    ∃ C : V →ₗ[ℂ] V, C.restrictScalars ℝ = N := by
  let C : V →ₗ[ℂ] V :=
    { toFun := N
      map_add' := N.map_add
      map_smul' := realLinear_map_complex_smul N z hz h }
  exact ⟨C, rfl⟩

end ComplexCentralizer

section RotationDerivative
variable {A V : Type*} [AddCommGroup A] [Module ℝ A]
  [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]

/-- A real derivative commuting with the fixed-plus-rotating representation
has no mixed blocks. Its normal block is complex-linear. -/
theorem rotation_commutant_blocks (L : A × V →ₗ[ℝ] A × V)
    (z : ℂ) (hz : z.im ≠ 0)
    (h : ∀ a v, L (a, z • v) = ((L (a, v)).1, z • (L (a, v)).2)) :
    ∃ (T : A →ₗ[ℝ] A) (N : V →ₗ[ℂ] V),
      L = T.prodMap (N.restrictScalars ℝ) := by
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz
  let T := (LinearMap.fst ℝ A V).comp (L.comp (LinearMap.inl ℝ A V))
  let N := (LinearMap.snd ℝ A V).comp (L.comp (LinearMap.inr ℝ A V))
  let P := (LinearMap.fst ℝ A V).comp (L.comp (LinearMap.inr ℝ A V))
  have hP (v : V) : P (z • v) = P v := by
    have hv := congrArg Prod.fst (h 0 v)
    exact hv
  have hPzero (v : V) : P v = 0 := by
    let u := (z - 1)⁻¹ • v
    have huv : z • u - u = v := by
      dsimp [u]
      calc
        z • ((z - 1)⁻¹ • v) - (z - 1)⁻¹ • v =
            (z - 1) • ((z - 1)⁻¹ • v) := by rw [sub_smul, one_smul]
        _ = v := by rw [smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr hz1), one_smul]
    rw [← huv, map_sub, hP, sub_self]
  have hQzero (a : A) : (L (a, 0)).2 = 0 := by
    have hv := congrArg Prod.snd (h a 0)
    simp only [smul_zero] at hv
    have hh : (z - 1) • (L (a, 0)).2 = 0 := by
      rw [sub_smul, one_smul, ← hv, sub_self]
    exact (smul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hz1)
  obtain ⟨C, hC⟩ := complexLinear_of_commutes_nonreal N z hz
    (fun v => congrArg Prod.snd (h 0 v))
  refine ⟨T, C, ?_⟩
  rw [hC]
  apply LinearMap.ext
  intro q
  apply Prod.ext
  · change (L q).1 = T q.1
    have he : q = (q.1, 0) + (0, q.2) := by simp
    rw [he, map_add]
    change T q.1 + P q.2 = _
    rw [hPzero, add_zero]
    simp
  · change (L q).2 = N q.2
    have he : q = (q.1, 0) + (0, q.2) := by simp
    rw [he, map_add]
    change (L (q.1, 0)).2 + N q.2 = _
    rw [hQzero, zero_add]
    simp

end RotationDerivative

section NormalDeterminant
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
  [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V]

theorem complex_real_det_nonneg (N : V →ₗ[ℂ] V) :
    0 ≤ (N.restrictScalars ℝ).det := by
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  exact Complex.normSq_nonneg _

theorem complex_real_det_pos (N : V →ₗ[ℂ] V) (hN : N.det ≠ 0) :
    0 < (N.restrictScalars ℝ).det := by
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  exact Complex.normSq_pos.mpr hN

end NormalDeterminant

section SimultaneousShift
open Set
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- A single real scalar regularizes any finite collection of normal blocks. -/
theorem exists_small_simultaneous_regular_shift {ι : Type*} [Fintype ι]
    (N : ι → Module.End ℂ V) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : ℝ, |s| < ε ∧ ∀ i, IsUnit (N i + algebraMap ℂ (Module.End ℂ V) (s : ℂ)) := by
  let bad : Set ℝ := ⋃ i, {r | -(r : ℂ) ∈ spectrum ℂ (N i)}
  have hbad : bad.Finite := Set.finite_iUnion (fun i =>
    (Module.End.finite_spectrum (N i)).preimage
      (fun _ _ _ _ h => Complex.ofReal_injective (neg_injective h)))
  obtain ⟨s, hs, hgood⟩ := (Set.Ioo_infinite (by linarith : -ε < ε)).exists_notMem_finite hbad
  refine ⟨s, abs_lt.mpr hs, fun i => ?_⟩
  have hn : -(s : ℂ) ∉ spectrum ℂ (N i) := by
    intro hh
    exact hgood (Set.mem_iUnion.mpr ⟨i, hh⟩)
  have hi := (spectrum.notMem_iff.mp hn).neg
  simpa only [map_neg, neg_sub, sub_neg_eq_add] using hi

end SimultaneousShift
end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
open scoped ContDiff
section EquivariantDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem equivariant_fderiv (f : E → E) (L : E ≃L[ℝ] E)
    (hf : Differentiable ℝ f) (he : ∀ x, f (L x) = L (f x)) (x : E) :
    (fderiv ℝ f (L x)).comp L.toContinuousLinearMap =
      L.toContinuousLinearMap.comp (fderiv ℝ f x) := by
  have h₁ := (hf (L x)).hasFDerivAt.comp x L.hasFDerivAt
  have h₂ := L.hasFDerivAt.comp x (hf x).hasFDerivAt
  have hh : f ∘ L = L ∘ f := funext he
  rw [hh] at h₁
  exact h₁.unique h₂

omit [FiniteDimensional ℝ E] in
theorem equivariant_fderiv_det (f : E → E) (L : E ≃L[ℝ] E)
    (hf : Differentiable ℝ f) (he : ∀ x, f (L x) = L (f x)) (x : E) :
    (fderiv ℝ f (L x)).det = (fderiv ℝ f x).det := by
  have h := congrArg (fun M : E →L[ℝ] E => M.det) (equivariant_fderiv f L hf he x)
  change ((fderiv ℝ f (L x)).toLinearMap.comp L.toLinearEquiv.toLinearMap).det =
    (L.toLinearEquiv.toLinearMap.comp (fderiv ℝ f x).toLinearMap).det at h
  rw [LinearMap.det_comp, LinearMap.det_comp, mul_comm] at h
  exact mul_left_cancel₀ L.toLinearEquiv.isUnit_det'.ne_zero h
end EquivariantDerivative

section FixedRegularization
variable {A V : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The complement of the fixed subspace. -/
def normalProjection : (A × V) →L[ℝ] (A × V) :=
  (ContinuousLinearMap.inr ℝ A V).comp (ContinuousLinearMap.snd ℝ A V)

@[simp] theorem normalProjection_apply (x : A × V) : normalProjection x = (0, x.2) := rfl

def normalShift (f : A × V → A × V) (s : ℝ) (x : A × V) := f x + s • normalProjection x

theorem normalShift_contDiff (f : A × V → A × V) (hf : ContDiff ℝ ∞ f) (s : ℝ) :
    ContDiff ℝ ∞ (normalShift f s) :=
  hf.add ((show ContDiff ℝ ∞ (fun _ : A × V => s) from contDiff_const).smul
    (normalProjection (A := A) (V := V)).contDiff)

theorem normalShift_fderiv (f : A × V → A × V) (hf : Differentiable ℝ f) (s : ℝ) (x : A × V) :
    fderiv ℝ (normalShift f s) x = fderiv ℝ f x + s • normalProjection :=
  ((hf x).hasFDerivAt.add ((normalProjection (A := A) (V := V)).hasFDerivAt.const_smul s)).fderiv

@[simp] theorem normalShift_fixed (f : A × V → A × V) (s : ℝ) (a : A) :
    normalShift f s (a, 0) = f (a, 0) := by simp [normalShift]

variable [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V]

def scalarRotation (z : ℂˣ) : (A × V) ≃L[ℝ] (A × V) :=
  (ContinuousLinearEquiv.refl ℝ A).prodCongr
    ((ContinuousLinearEquiv.smulLeft z : V ≃L[ℂ] V).restrictScalars ℝ)

@[simp] theorem scalarRotation_apply (z : ℂˣ) (q : A × V) :
    scalarRotation z q = (q.1, (z : ℂ) • q.2) := rfl

/-- At a fixed point the derivative splits with a complex-linear normal block. -/
theorem fixed_fderiv_blocks (f : A × V → A × V) (hf : Differentiable ℝ f)
    (z : ℂˣ) (hz : (z : ℂ).im ≠ 0)
    (he : ∀ q, f (scalarRotation z q) = scalarRotation z (f q)) (a : A) :
    ∃ (T : A →ₗ[ℝ] A) (N : V →ₗ[ℂ] V),
      (fderiv ℝ f (a, 0)).toLinearMap = T.prodMap (N.restrictScalars ℝ) := by
  apply rotation_commutant_blocks _ (z : ℂ) hz
  intro b v
  have h := congrArg (fun L : (A × V) →L[ℝ] (A × V) => L (b, v)) (equivariant_fderiv f (scalarRotation z) hf he (a, 0))
  simpa using h

variable [FiniteDimensional ℝ A] [FiniteDimensional ℂ V]

/-- Scalar shifts have the claimed fixed-block Jacobian, with no chart convention. -/
theorem normalShift_fixed_det (f : A × V → A × V) (hf : Differentiable ℝ f)
    (a : A) (T : A →ₗ[ℝ] A) (N : V →ₗ[ℂ] V)
    (h : (fderiv ℝ f (a, 0)).toLinearMap = T.prodMap (N.restrictScalars ℝ)) (s : ℝ) :
    (fderiv ℝ (normalShift f s) (a, 0)).det =
      T.det * ((N + algebraMap ℂ (Module.End ℂ V) (s : ℂ)).restrictScalars ℝ).det := by
  let : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  rw [normalShift_fderiv f hf]
  have he : (fderiv ℝ f (a, 0) + s • normalProjection).toLinearMap =
      T.prodMap ((N + algebraMap ℂ (Module.End ℂ V) (s : ℂ)).restrictScalars ℝ) := by
    apply LinearMap.ext
    intro q
    have hh := LinearMap.congr_fun h q
    change (fderiv ℝ f (a, 0)) q + s • (0, q.2) = _
    change (fderiv ℝ f (a, 0)) q = (T q.1, N q.2) at hh
    rw [hh]
    simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero,
      LinearMap.prodMap_apply, LinearMap.restrictScalars_apply, LinearMap.add_apply,
      Module.algebraMap_end_apply]
    congr 2
    exact (IsScalarTower.algebraMap_smul ℂ s q.2).symm
  change (fderiv ℝ f (a, 0) + s • normalProjection).toLinearMap.det = _
  rw [he, LinearMap.det_prodMap]


def fixedRestriction (f : A × V → A × V) (a : A) : A := (f (a, 0)).1

omit [FiniteDimensional ℝ A] [FiniteDimensional ℂ V] in
theorem fixedRestriction_fderiv (f : A × V → A × V) (hf : Differentiable ℝ f)
    (a : A) (T : A →ₗ[ℝ] A) (N : V →ₗ[ℂ] V)
    (h : (fderiv ℝ f (a, 0)).toLinearMap = T.prodMap (N.restrictScalars ℝ)) :
    (fderiv ℝ (fixedRestriction f) a).toLinearMap = T := by
  have hd := (ContinuousLinearMap.fst ℝ A V).hasFDerivAt.comp a
    ((hf (a, 0)).hasFDerivAt.comp a (ContinuousLinearMap.inl ℝ A V).hasFDerivAt)
  have hfun : (ContinuousLinearMap.fst ℝ A V) ∘ (f ∘ (ContinuousLinearMap.inl ℝ A V)) =
      fixedRestriction f := rfl
  rw [hfun] at hd
  rw [hd.fderiv]
  apply LinearMap.ext
  intro q
  exact congrArg Prod.fst (LinearMap.congr_fun h (q, 0))

/-- Simultaneously regularize the finite fixed fiber, retaining its tangent sign. -/
theorem exists_normalShift_regular_fixed (f : A × V → A × V) (hf : Differentiable ℝ f)
    (z : ℂˣ) (hz : (z : ℂ).im ≠ 0)
    (he : ∀ q, f (scalarRotation z q) = scalarRotation z (f q))
    (S : Finset A) (c : ℝ) (hc : c ≠ 0)
    (hT : ∀ a ∈ S, (fderiv ℝ (fixedRestriction f) a).det = c)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℝ, |s| < ε ∧ ∀ a ∈ S,
      (fderiv ℝ (normalShift f s) (a, 0)).det ≠ 0 ∧
      (0 < (fderiv ℝ (normalShift f s) (a, 0)).det ↔ 0 < c) := by
  classical
  choose T N hblock using (fun a : S => fixed_fderiv_blocks f hf z hz he a.val)
  obtain ⟨s, hs, hregular⟩ := exists_small_simultaneous_regular_shift N hε
  refine ⟨s, hs, fun a ha => ?_⟩
  let i : S := ⟨a, ha⟩
  have ht : (T i).det = c := by
    rw [← fixedRestriction_fderiv f hf a (T i) (N i) (hblock i)]
    exact hT a ha
  have hn : 0 < ((N i + algebraMap ℂ (Module.End ℂ V) (s : ℂ)).restrictScalars ℝ).det :=
    complex_real_det_pos _ (LinearMap.isUnit_det _ (hregular i)).ne_zero
  rw [normalShift_fixed_det f hf a (T i) (N i) (hblock i), ht]
  exact ⟨mul_ne_zero hc hn.ne', mul_pos_iff_of_pos_right hn⟩

end FixedRegularization
end EilenbergGanea

open Set Filter Topology
namespace EilenbergGanea
section LinearParameters
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def linearPerturbation (f : E → E) (T : ι → E → (E →L[ℝ] E))
    (x : E) (p : ι → E) : E := f x + ∑ j, T j x (p j)

def linearPerturbationDerivative (f : E → E) (T : ι → E → (E →L[ℝ] E))
    (x : E) (p : ι → E) : E →L[ℝ] E :=
  fderiv ℝ f x + ∑ j, (fderiv ℝ (T j) x).flip (p j)

omit [DecidableEq ι] in
theorem linearPerturbation_hasFDerivAt (f : E → E) (T : ι → E → (E →L[ℝ] E))
    {x : E} (hf : DifferentiableAt ℝ f x) (hT : ∀ j, DifferentiableAt ℝ (T j) x)
    (p : ι → E) : HasFDerivAt (fun z => linearPerturbation f T z p)
      (linearPerturbationDerivative f T x p) x := by
  apply hf.hasFDerivAt.add
  apply HasFDerivAt.fun_sum
  intro j _
  simpa using (hT j).hasFDerivAt.clm_apply (hasFDerivAt_const (p j) x)

def linearSolvedParameter (f : E → E) (T : ι → E → (E →L[ℝ] E))
    (i : ι) (q : ι → E) : ι → E :=
  Function.update q i (-(Ring.inverse (T i (q i))
    (f (q i) + ∑ j ∈ Finset.univ.erase i, T j (q i) (q j))))

theorem linearSolvedParameter_outside (f : E → E) (T : ι → E → (E →L[ℝ] E))
    (i j : ι) (hji : j ≠ i) :
    (fun q => linearSolvedParameter f T i q j) = fun q => q j := by
  funext q
  exact Function.update_of_ne hji _ _

theorem inverse_apply_cancel (A : E →L[ℝ] E) (hA : IsUnit A) (v : E) :
    Ring.inverse A (A v) = v := by
  exact congrArg (fun B : E →L[ℝ] E => B v) (Ring.inverse_mul_cancel A hA)

theorem apply_inverse_cancel (A : E →L[ℝ] E) (hA : IsUnit A) (v : E) :
    A (Ring.inverse A v) = v := by
  exact congrArg (fun B : E →L[ℝ] E => B v) (Ring.mul_inverse_cancel A hA)

theorem linearSolvedParameter_root (f : E → E) (T : ι → E → (E →L[ℝ] E))
    (i : ι) (q : ι → E) (hi : IsUnit (T i (q i))) :
    linearPerturbation f T (q i) (linearSolvedParameter f T i q) = 0 := by
  rw [linearPerturbation, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have he : (∑ j ∈ Finset.univ.erase i, T j (q i) (linearSolvedParameter f T i q j)) =
      ∑ j ∈ Finset.univ.erase i, T j (q i) (q j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [linearSolvedParameter, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [he]
  simp only [linearSolvedParameter, Function.update_self, map_neg,
    apply_inverse_cancel _ hi]
  abel

variable [FiniteDimensional ℝ E]

theorem linearSolvedParameter_differentiableAt (f : E → E) (T : ι → E → (E →L[ℝ] E))
    (i : ι) (q : ι → E) (hf : DifferentiableAt ℝ f (q i))
    (hT : ∀ j, DifferentiableAt ℝ (T j) (q i)) (hi : IsUnit (T i (q i))) :
    DifferentiableAt ℝ (linearSolvedParameter f T i) q := by
  have hproj := differentiableAt_apply i q (𝕜 := ℝ)
  apply differentiableAt_pi.mpr
  intro j
  by_cases hj : j = i
  · subst j
    simp only [linearSolvedParameter, Function.update_self]
    apply DifferentiableAt.neg
    apply DifferentiableAt.clm_apply
    · exact ((hT i).inverse hi).comp q hproj
    · exact (hf.comp q hproj).add (DifferentiableAt.fun_sum (fun k _ =>
        ((hT k).comp q hproj).clm_apply (differentiableAt_apply k q)))
  · simpa only [linearSolvedParameter_outside f T i j hj] using differentiableAt_apply j q (𝕜 := ℝ)

omit [FiniteDimensional ℝ E] in
theorem linearSolvedParameter_fderiv_outside (f : E → E) (T : ι → E → (E →L[ℝ] E))
    (i j : ι) (hji : j ≠ i) (q : ι → E)
    (hG : DifferentiableAt ℝ (linearSolvedParameter f T i) q) :
    (ContinuousLinearMap.proj j : (ι → E) →L[ℝ] E).comp
      (fderiv ℝ (linearSolvedParameter f T i) q) = ContinuousLinearMap.proj j := by
  have h := ((ContinuousLinearMap.proj j : (ι → E) →L[ℝ] E)).hasFDerivAt.comp q hG.hasFDerivAt
  have he : (ContinuousLinearMap.proj j : (ι → E) →L[ℝ] E) ∘
      linearSolvedParameter f T i = fun q => q j :=
    linearSolvedParameter_outside f T i j hji
  rw [he] at h
  exact h.unique ((ContinuousLinearMap.proj j : (ι → E) →L[ℝ] E)).hasFDerivAt

theorem linearSolvedParameter_differential_relation
    (f : E → E) (T : ι → E → (E →L[ℝ] E)) (i : ι) (q : ι → E)
    (hf : DifferentiableAt ℝ f (q i)) (hT : ∀ j, DifferentiableAt ℝ (T j) (q i))
    (hi : IsUnit (T i (q i))) (v : E) :
    linearPerturbationDerivative f T (q i) (linearSolvedParameter f T i q) v +
      ∑ j, T j (q i) ((fderiv ℝ (linearSolvedParameter f T i) q (Pi.single i v)) j) = 0 := by
  let G := linearSolvedParameter f T i
  have hG := linearSolvedParameter_differentiableAt f T i q hf hT hi
  have hfi := hf.hasFDerivAt.comp q ((ContinuousLinearMap.proj i : (ι → E) →L[ℝ] E)).hasFDerivAt
  have hx := hfi.fun_add (HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    ((hT j).hasFDerivAt.comp q ((ContinuousLinearMap.proj i : (ι → E) →L[ℝ] E)).hasFDerivAt).clm_apply
      (((ContinuousLinearMap.proj j : (ι → E) →L[ℝ] E)).hasFDerivAt.comp q hG.hasFDerivAt)))
  have hz : (fun t => linearPerturbation f T (t i) (G t)) =ᶠ[𝓝 q] fun _ => 0 := by
    have hcont : ContinuousAt (fun t : ι → E => T i (t i)) q :=
      ((hT i).comp q (differentiableAt_apply i q)).continuousAt
    have he : ∀ᶠ t in 𝓝 q, IsUnit (T i (t i)) :=
      hcont (Units.isOpen.mem_nhds hi)
    filter_upwards [he] with t ht
    exact linearSolvedParameter_root f T i t ht
  have hc := (hasFDerivAt_const (𝕜 := ℝ) (0 : E) q).congr_of_eventuallyEq hz
  have he := congrArg (fun l : (ι → E) →L[ℝ] E => l (Pi.single i v)) (hx.unique hc)
  simp only [add_apply, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.flip_apply,
    Pi.single_eq_same, zero_apply, Finset.sum_add_distrib] at he
  simp only [linearPerturbationDerivative, add_apply, sum_apply, ContinuousLinearMap.flip_apply]
  dsimp [G] at he
  exact (by convert he using 1; abel)

omit [FiniteDimensional ℝ E] in
theorem linearSolvedParameter_recovers_root (f : E → E) (T : ι → E → (E →L[ℝ] E))
    (i : ι) (x : E) (p : ι → E) (hi : IsUnit (T i x))
    (hroot : linearPerturbation f T x p = 0) :
    linearSolvedParameter f T i (Function.update p i x) = p := by
  have he : (∑ j ∈ Finset.univ.erase i, T j x (Function.update p i x j)) =
      ∑ j ∈ Finset.univ.erase i, T j x (p j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hs : T i x (p i) = -(f x + ∑ j ∈ Finset.univ.erase i, T j x (p j)) := by
    rw [linearPerturbation, ← Finset.sum_erase_add _ _ (Finset.mem_univ i),
      ← add_assoc] at hroot
    exact eq_neg_of_add_eq_zero_right hroot
  funext j
  by_cases hj : j = i
  · subst j
    simp only [linearSolvedParameter, Function.update_self, he]
    rw [← map_neg, ← hs, inverse_apply_cancel _ hi]
  · simp [linearSolvedParameter, Function.update_of_ne hj]

theorem linearSolvedParameter_critical (f : E → E) (T : ι → E → (E →L[ℝ] E))
    (i : ι) (q : ι → E) (hf : DifferentiableAt ℝ f (q i))
    (hT : ∀ j, DifferentiableAt ℝ (T j) (q i)) (hi : IsUnit (T i (q i)))
    (hcrit : (linearPerturbationDerivative f T (q i) (linearSolvedParameter f T i q)).det = 0) :
    (fderiv ℝ (linearSolvedParameter f T i) q).det = 0 := by
  have hG := linearSolvedParameter_differentiableAt f T i q hf hT hi
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hcrit)
  change linearPerturbationDerivative f T (q i) (linearSolvedParameter f T i q) v = 0 at hv
  let w := fderiv ℝ (linearSolvedParameter f T i) q (Pi.single i v)
  have hw (j : ι) (hji : j ≠ i) : w j = 0 := by
    have he := congrArg (fun l : (ι → E) →L[ℝ] E => l (Pi.single i v))
      (linearSolvedParameter_fderiv_outside f T i j hji q hG)
    simpa [w, Pi.single_eq_of_ne hji] using he
  have hrel := linearSolvedParameter_differential_relation f T i q hf hT hi v
  rw [hv, zero_add] at hrel
  have hwi : w i = 0 := by
    have hs : (∑ j, T j (q i) (w j)) = T i (q i) (w i) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        simp [hw j hji]
      · simp
    rw [hs] at hrel
    have he := congrArg (fun v => Ring.inverse (T i (q i)) v) hrel
    simpa only [inverse_apply_cancel _ hi, map_zero] using he
  apply LinearMap.det_eq_zero_iff_ker_ne_bot.mpr
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨Pi.single i v, ?_, ?_⟩
  · change w = 0
    funext j
    by_cases hj : j = i
    · subst j; exact hwi
    · exact hw j hj
  · intro he
    apply hv0
    simpa using congrFun he i

/-- Transversality with source-dependent linear parameter blocks, including
finite equivariant bump perturbations. Only invertibility of a single active
block is required at each root. -/
theorem ae_regular_linear_parameters [MeasurableSpace E] [BorelSpace E]
    (μ : MeasureTheory.Measure (ι → E)) [μ.IsAddHaarMeasure]
    (f : E → E) (T : ι → E → (E →L[ℝ] E)) (s : Set E)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hT : ∀ i x, x ∈ s → DifferentiableAt ℝ (T i) x) :
    ∀ᵐ p ∂μ, ∀ x ∈ s, linearPerturbation f T x p = 0 →
      (∃ i, IsUnit (T i x)) → (linearPerturbationDerivative f T x p).det ≠ 0 := by
  let C : ι → Set (ι → E) := fun i =>
    {q | q i ∈ s ∧ IsUnit (T i (q i)) ∧ (fderiv ℝ (linearSolvedParameter f T i) q).det = 0}
  have hnull (i : ι) : μ (linearSolvedParameter f T i '' C i) = 0 := by
    apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
    · intro q hq
      exact (linearSolvedParameter_differentiableAt f T i q (hf _ hq.1)
        (fun j => hT j _ hq.1) hq.2.1).hasFDerivAt.hasFDerivWithinAt
    · intro q hq
      exact hq.2.2
  have hae : ∀ᵐ p ∂μ, p ∉ ⋃ i, linearSolvedParameter f T i '' C i := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using MeasureTheory.measure_iUnion_null hnull
  filter_upwards [hae] with p hp
  intro x hs hx ⟨i, hi⟩ hcrit
  let q := Function.update p i x
  have hqi : q i = x := Function.update_self _ _ _
  have hGq : linearSolvedParameter f T i q = p :=
    linearSolvedParameter_recovers_root f T i x p hi hx
  apply hp
  apply Set.mem_iUnion.mpr
  refine ⟨i, q, ⟨?_, ?_, ?_⟩, hGq⟩
  · simpa only [hqi] using hs
  · simpa only [hqi] using hi
  · apply linearSolvedParameter_critical f T i q
        (by simpa only [hqi] using hf x hs)
        (fun j => by simpa only [hqi] using hT j x hs)
    · simpa only [hqi] using hi
    · simpa only [hqi, hGq] using hcrit

end LinearParameters
end EilenbergGanea
open scoped ContDiff
open Set Filter Topology
namespace EilenbergGanea
section EquivariantBumps
variable {G E : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def equivariantBumpOperator (ρ : G →* E ≃L[ℝ] E) (b : E → ℝ) (x : E) : E →L[ℝ] E :=
  ∑ g, b (ρ g⁻¹ x) • (ρ g : E →L[ℝ] E)

omit [Fintype G] in
theorem representation_cancel (ρ : G →* E ≃L[ℝ] E) (g : G) (x : E) :
    ρ g⁻¹ (ρ g x) = x := by
  change ((ρ g⁻¹) * ρ g) x = x
  rw [← map_mul, inv_mul_cancel, map_one]
  rfl

omit [Fintype G] in
theorem representation_mul_apply (ρ : G →* E ≃L[ℝ] E) (g h : G) (x : E) :
    ρ (g * h) x = ρ g (ρ h x) := by rw [map_mul]; rfl

theorem equivariantBumpOperator_equivariant (ρ : G →* E ≃L[ℝ] E) (b : E → ℝ)
    (h : G) (x : E) :
    equivariantBumpOperator ρ b (ρ h x) =
      (ρ h : E →L[ℝ] E).comp (equivariantBumpOperator ρ b x) := by
  ext v
  simp only [equivariantBumpOperator, sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply, map_sum, map_smul]
  symm
  apply Fintype.sum_equiv (Equiv.mulLeft h)
  intro g
  change b (ρ g⁻¹ x) • ρ h (ρ g v) =
    b (ρ (h * g)⁻¹ (ρ h x)) • ρ (h * g) v
  simp only [mul_inv_rev, representation_mul_apply, representation_cancel]

theorem equivariantBumpOperator_contDiff (ρ : G →* E ≃L[ℝ] E) (b : E → ℝ)
    (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (equivariantBumpOperator ρ b) := by
  apply ContDiff.sum
  intro g _
  exact (hb.comp (ρ g⁻¹).contDiff).smul contDiff_const

theorem unit_smul_equiv (a : ℝ) (ha : a ≠ 0) (e : E ≃L[ℝ] E) :
    IsUnit (a • (e : E →L[ℝ] E)) := by
  refine ⟨⟨a • (e : E →L[ℝ] E), a⁻¹ • (e.symm : E →L[ℝ] E), ?_, ?_⟩, rfl⟩
  · ext v
    simp [smul_smul, ha]
  · ext v
    simp [smul_smul, ha]

theorem equivariantBumpOperator_isUnit (ρ : G →* E ≃L[ℝ] E) (b : E → ℝ)
    (hbd : Pairwise fun g h : G => Disjoint (ρ g '' tsupport b) (ρ h '' tsupport b))
    (x : E) (g : G) (hg : b (ρ g⁻¹ x) ≠ 0) : IsUnit (equivariantBumpOperator ρ b x) := by
  have hx (k : G) (hk : b (ρ k⁻¹ x) ≠ 0) : x ∈ ρ k '' tsupport b :=
    ⟨ρ k⁻¹ x, subset_tsupport b hk, by simpa using representation_cancel ρ k⁻¹ x⟩
  have he : equivariantBumpOperator ρ b x = b (ρ g⁻¹ x) • (ρ g : E →L[ℝ] E) := by
    apply Finset.sum_eq_single g
    · intro h _ hh
      have hh0 : b (ρ h⁻¹ x) = 0 := by
        by_contra hh0
        exact Set.disjoint_left.mp (hbd hh) (hx h hh0) (hx g hg)
      simp only [hh0, zero_smul]
    · simp
  rw [he]
  exact unit_smul_equiv _ hg _

/-- A free orbit for a finite linear action has a neighborhood with pairwise
disjoint translates. No isometry hypothesis or metric constants are needed. -/
theorem free_orbit_disjoint_neighborhood (ρ : G →* E ≃L[ℝ] E) (x : E)
    (hx : ∀ g : G, ρ g x = x → g = 1) (W : Set E) (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧
      Pairwise fun g h : G => Disjoint (ρ g '' V) (ρ h '' V) := by
  classical
  have hsep (g : {g : G // g ≠ 1}) :
      ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ Disjoint U (ρ g.val '' U) := by
    have hgx : x ≠ ρ g.val x := fun he => g.property (hx _ he.symm)
    obtain ⟨A, B, hA, hB, hxA, hxB, hAB⟩ := t2_separation hgx
    refine ⟨A ∩ (ρ g.val ⁻¹' B), hA.inter (hB.preimage (ρ g.val).continuous), ⟨hxA, hxB⟩, ?_⟩
    apply hAB.mono inter_subset_left
    rintro y ⟨z, hz, rfl⟩
    exact hz.2
  choose U hU hxU hdU using hsep
  let V : Set E := W ∩ ⋂ g : {g : G // g ≠ 1}, U g
  have hVo : IsOpen V := hW.inter (isOpen_iInter_of_finite hU)
  have hxV : x ∈ V := ⟨hxW, mem_iInter.mpr hxU⟩
  refine ⟨V, hVo, hxV, inter_subset_left, ?_⟩
  intro g h hgh
  apply Set.disjoint_left.mpr
  rintro y ⟨a, ha, rfl⟩ ⟨b, hb, he⟩
  have hk : g⁻¹ * h ≠ 1 := by
    intro heq
    apply hgh
    have := congrArg (fun k => g * k) heq
    simpa only [← mul_assoc, mul_inv_cancel, one_mul, mul_one] using this.symm
  have haU : a ∈ U ⟨g⁻¹ * h, hk⟩ := mem_iInter.mp ha.2 _
  have hbU : b ∈ U ⟨g⁻¹ * h, hk⟩ := mem_iInter.mp hb.2 _
  apply Set.disjoint_left.mp (hdU ⟨g⁻¹ * h, hk⟩) haU
  refine ⟨b, hbU, ?_⟩
  rw [representation_mul_apply, he, representation_cancel]

variable [FiniteDimensional ℝ E]

/-- The bump family used in the free part of the localized-degree argument.
Its complete closed support has disjoint translates, so each active parameter
block is invertible. -/
theorem free_orbit_smooth_bump (ρ : G →* E ≃L[ℝ] E) (x : E)
    (hx : ∀ g : G, ρ g x = x → g = 1) (W : Set E) (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ b : E → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧ tsupport b ⊆ W ∧ b x = 1 ∧
      Pairwise fun g h : G => Disjoint (ρ g '' tsupport b) (ρ h '' tsupport b) := by
  obtain ⟨V, hV, hxV, hVW, hdisj⟩ := free_orbit_disjoint_neighborhood ρ x hx W hW hxW
  obtain ⟨b, hbV, hcb, hdb, _, hbx⟩ := exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hV.mem_nhds hxV)
  refine ⟨b, hdb, hcb, hbV.trans hVW, hbx, ?_⟩
  intro g h hgh
  exact (hdisj hgh).mono (image_mono hbV) (image_mono hbV)

end EquivariantBumps
end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
open scoped ContDiff
section CompactRootStability
variable {P X Y : Type*} [TopologicalSpace P] [TopologicalSpace X]
  [TopologicalSpace Y] [CompactSpace X] [T1Space Y]

theorem compact_root_good_stability (f : P × X → Y) (hf : Continuous f)
    (y : Y) (V : Set (P × X)) (hV : IsOpen V) (p₀ : P)
    (h₀ : ∀ x, f (p₀, x) = y → (p₀, x) ∈ V) :
    ∀ᶠ p in 𝓝 p₀, ∀ x, f (p, x) = y → (p, x) ∈ V := by
  let C : Set (P × X) := {q | f q = y} ∩ Vᶜ
  have hC : IsClosed C := (isClosed_singleton.preimage hf).inter hV.isClosed_compl
  have hn : p₀ ∉ Prod.fst '' C := by
    rintro ⟨⟨p, x⟩, ⟨hr, hv⟩, rfl⟩
    exact hv (h₀ x hr)
  filter_upwards [(isClosedMap_fst_of_compactSpace _ hC).isOpen_compl.mem_nhds hn] with p hp
  intro x hr
  by_contra hv
  exact hp ⟨(p, x), ⟨hr, hv⟩, rfl⟩
end CompactRootStability

section CompactFreeBumps
universe uE uG
variable {G : Type uG} {E : Type uE} [Group G] [Fintype G] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem compact_free_bump_family (ρ : G →* E ≃L[ℝ] E)
    (K W : Set E) (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hfree : ∀ x ∈ K, ∀ g : G, ρ g x = x → g = 1) :
    ∃ (ι : Type uE) (_ : Fintype ι) (b : ι → E → ℝ),
      (∀ i, ContDiff ℝ ∞ (b i) ∧ HasCompactSupport (b i) ∧ tsupport (b i) ⊆ W ∧
        Pairwise fun g h : G => Disjoint (ρ g '' tsupport (b i)) (ρ h '' tsupport (b i))) ∧
      (∀ x ∈ K, ∃ i, IsUnit (equivariantBumpOperator ρ (b i) x)) := by
  classical
  have hb (x : K) := free_orbit_smooth_bump ρ x.val (hfree x.val x.property)
    W hW (hKW x.property)
  choose b hbd hbc hbs hbx hdis using hb
  have hcov : K ⊆ ⋃ x : K, {y | b x y ≠ 0} := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, by simp [hbx]⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => {y | b x y ≠ 0})
    (fun x => isOpen_ne_fun (hbd x).continuous continuous_const) hcov
  refine ⟨{x // x ∈ t}, inferInstance, fun i => b i.val, ?_, ?_⟩
  · exact fun i => ⟨hbd i.val, hbc i.val, hbs i.val, hdis i.val⟩
  · intro x hx
    obtain ⟨i, hi, hbix⟩ := Set.mem_iUnion₂.mp (ht hx)
    refine ⟨⟨i, hi⟩, equivariantBumpOperator_isUnit ρ (b i) (hdis i) x 1 ?_⟩
    rw [inv_one, map_one]
    exact hbix

end CompactFreeBumps

section LinearRegularization
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [DecidableEq ι] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem linearPerturbation_contDiff (f : E → E) (T : ι → E → (E →L[ℝ] E))
    (hf : ContDiff ℝ ∞ f) (hT : ∀ i, ContDiff ℝ ∞ (T i)) :
    ContDiff ℝ ∞ (fun q : (ι → E) × E => linearPerturbation f T q.2 q.1) := by
  apply (hf.comp contDiff_snd).add
  apply ContDiff.sum
  intro i _
  exact ((hT i).comp contDiff_snd).clm_apply ((contDiff_apply ℝ E i).comp contDiff_fst)

omit [DecidableEq ι] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem linearPerturbationDerivative_continuous (f : E → E) (T : ι → E → (E →L[ℝ] E))
    (hf : ContDiff ℝ ∞ f) (hT : ∀ i, ContDiff ℝ ∞ (T i)) :
    Continuous (fun q : (ι → E) × E => linearPerturbationDerivative f T q.2 q.1) := by
  apply (hf.continuous_fderiv (by norm_num)).comp continuous_snd |>.add
  apply continuous_finsetSum
  intro i _
  exact ((ContinuousLinearMap.flipₗᵢ ℝ E E E).continuous.comp
    (((hT i).continuous_fderiv (by norm_num)).comp continuous_snd)).clm_apply
    ((continuous_apply i).comp continuous_fst)

/-- A finite linear bump family regularizes all roots on a compact set, provided
it has an invertible block at every initially critical root. The parameters
can be chosen in any prescribed neighborhood of zero. -/
theorem exists_regular_linear_perturbation
    (μ : MeasureTheory.Measure (ι → E)) [μ.IsAddHaarMeasure]
    (f : E → E) (T : ι → E → (E →L[ℝ] E))
    (hf : ContDiff ℝ ∞ f) (hT : ∀ i, ContDiff ℝ ∞ (T i))
    (K : Set E) (hK : IsCompact K)
    (hcover : ∀ x ∈ K, f x = 0 → (fderiv ℝ f x).det = 0 → ∃ i, IsUnit (T i x))
    (U : Set (ι → E)) (hU : U ∈ 𝓝 0) :
    ∃ p ∈ U, ∀ x ∈ K, linearPerturbation f T x p = 0 →
      (linearPerturbationDerivative f T x p).det ≠ 0 := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : (ι → E) × K → E := fun q => linearPerturbation f T q.2.val q.1
  let V : Set ((ι → E) × K) := {q |
    (linearPerturbationDerivative f T q.2.val q.1).det ≠ 0 ∨ ∃ i, IsUnit (T i q.2.val)}
  have hc : Continuous (fun q : (ι → E) × K => (q.1, q.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hV : IsOpen V := by
    have hd : IsOpen {q : (ι → E) × K |
        (linearPerturbationDerivative f T q.2.val q.1).det ≠ 0} :=
      isOpen_ne_fun (ContinuousLinearMap.continuous_det.comp
        ((linearPerturbationDerivative_continuous f T hf hT).comp hc)) continuous_const
    have ho := isOpen_iUnion (fun i => Units.isOpen.preimage ((hT i).continuous.comp
      (continuous_subtype_val.comp (continuous_snd : Continuous (Prod.snd : (ι → E) × K → K)))))
    have he : {q : (ι → E) × K | ∃ i, IsUnit (T i q.2.val)} =
        ⋃ i, (T i ∘ Subtype.val ∘ Prod.snd) ⁻¹' {a | IsUnit a} := by
      ext q
      simp
    have hi : IsOpen {q : (ι → E) × K | ∃ i, IsUnit (T i q.2.val)} := he ▸ ho
    exact hd.union hi
  have h₀ : ∀ x : K, F (0, x) = 0 → ((0 : ι → E), x) ∈ V := by
    intro x hx
    by_cases hd : (fderiv ℝ f x.val).det = 0
    · exact Or.inr (hcover x.val x.property (by simpa [F, linearPerturbation] using hx) hd)
    · exact Or.inl (by simpa [linearPerturbationDerivative] using hd)
  have he := compact_root_good_stability F ((linearPerturbation_contDiff f T hf hT).continuous.comp hc)
    0 V hV 0 h₀
  have hdense : Dense {p : ι → E | ∀ x ∈ K, linearPerturbation f T x p = 0 →
      (∃ i, IsUnit (T i x)) → (linearPerturbationDerivative f T x p).det ≠ 0} :=
    MeasureTheory.Measure.dense_of_ae (ae_regular_linear_parameters μ f T K
      (fun x _ => hf.differentiable (by norm_num) x)
      (fun i x _ => (hT i).differentiable (by norm_num) x))
  obtain ⟨p, hpreg, hpU, hpgood⟩ := hdense.inter_nhds_nonempty (inter_mem hU he)
  refine ⟨p, hpU, ?_⟩
  intro x hx hr
  rcases hpgood ⟨x, hx⟩ hr with hd | hi
  · exact hd
  · exact hpreg x hx hr hi

end LinearRegularization
end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
section EquivariantRegularization
universe uE uG
variable {G : Type uG} {E : Type uE} [Group G] [Fintype G] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem equivariantBumpOperator_eventually_zero_outside
    (ρ : G →* E ≃L[ℝ] E) (b : E → ℝ) (W : Set E)
    (hb : tsupport b ⊆ W) (hinv : ∀ g x, x ∈ W → ρ g x ∈ W)
    (x : E) (hx : x ∉ W) : equivariantBumpOperator ρ b =ᶠ[𝓝 x] 0 := by
  have hzero (a : G) : ∀ᶠ y in 𝓝 x, b (ρ a⁻¹ y) = 0 := by
    have hn : ρ a⁻¹ x ∉ tsupport b := by
      intro hs
      have hw := hinv a (ρ a⁻¹ x) (hb hs)
      have he : ρ a (ρ a⁻¹ x) = x := by
        rw [← representation_mul_apply, mul_inv_cancel, map_one]
        rfl
      exact hx (he ▸ hw)
    filter_upwards [((isClosed_tsupport b).preimage (ρ a⁻¹).continuous).isOpen_compl.mem_nhds hn]
      with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  filter_upwards [Filter.eventually_all.mpr hzero] with y hy
  change (∑ a : G, b (ρ a⁻¹ y) • (ρ a : E →L[ℝ] E)) = 0
  apply Finset.sum_eq_zero
  intro a _
  rw [hy a, zero_smul]

/-- The free-action regularization step. Critical roots must lie in the free
locus, but already regular fixed roots need not. The perturbation is unchanged
outside any chosen invariant open neighborhood of the critical roots. -/
theorem exists_equivariant_regular_perturbation
    (ρ : G →* E ≃L[ℝ] E) (f : E → E) (hf : ContDiff ℝ ∞ f)
    (heq : ∀ g x, f (ρ g x) = ρ g (f x))
    (K W : Set E) (hK : IsCompact K) (hW : IsOpen W)
    (hinv : ∀ g x, x ∈ W → ρ g x ∈ W)
    (hcritical : ∀ x ∈ K, f x = 0 → (fderiv ℝ f x).det = 0 →
      x ∈ W ∧ ∀ g : G, ρ g x = x → g = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : E → E, ContDiff ℝ ∞ g ∧ (∀ a x, g (ρ a x) = ρ a (g x)) ∧
      (∀ x ∉ W, g =ᶠ[𝓝 x] f) ∧ (∀ x ∈ K, ‖g x - f x‖ < ε) ∧
      ∀ x ∈ K, g x = 0 → (fderiv ℝ g x).det ≠ 0 := by
  classical
  let A : Set E := {x ∈ K | f x = 0 ∧ (fderiv ℝ f x).det = 0}
  have hA : IsCompact A := hK.inter_right
    ((isClosed_singleton.preimage hf.continuous).inter
      (isClosed_singleton.preimage (ContinuousLinearMap.continuous_det.comp
        (hf.continuous_fderiv (by norm_num)))))
  obtain ⟨ι, hι, b, hb, hcover⟩ := compact_free_bump_family ρ A W hA hW
    (fun x hx => (hcritical x hx.1 hx.2.1 hx.2.2).1)
    (fun x hx => (hcritical x hx.1 hx.2.1 hx.2.2).2)
  let := hι
  let T : ι → E → (E →L[ℝ] E) := fun i => equivariantBumpOperator ρ (b i)
  have hT (i : ι) : ContDiff ℝ ∞ (T i) := equivariantBumpOperator_contDiff ρ _ (hb i).1
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun q : (ι → E) × K => (q.1, q.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hopen : IsOpen {q : (ι → E) × K |
      ‖linearPerturbation f T q.2.val q.1 - f q.2.val‖ < ε} :=
    isOpen_lt (((linearPerturbation_contDiff f T hf hT).continuous.comp hc).sub
      (hf.continuous.comp (continuous_subtype_val.comp continuous_snd))).norm continuous_const
  have hsmall : ∀ᶠ p : ι → E in 𝓝 0,
      ∀ x : K, ‖linearPerturbation f T x.val p - f x.val‖ < ε := by
    have h := compact_root_good_stability (fun _ : (ι → E) × K => (0 : ℝ))
      continuous_const (0 : ℝ) _ hopen (0 : ι → E) (by
        intro x _
        simpa [linearPerturbation] using hε)
    filter_upwards [h] with p hp
    exact fun x => hp x rfl
  obtain ⟨p, hp, hreg⟩ := exists_regular_linear_perturbation
    (Module.finBasis ℝ (ι → E)).addHaar f T hf hT K hK
    (fun x hx hr hd => hcover x ⟨hx, hr, hd⟩) _ hsmall
  refine ⟨fun x => linearPerturbation f T x p, ?_, ?_, ?_, ?_, ?_⟩
  · exact (linearPerturbation_contDiff f T hf hT).comp (contDiff_const.prodMk contDiff_id)
  · intro a x
    simp only [linearPerturbation, heq, map_add, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun L : E →L[ℝ] E => L (p i)) (equivariantBumpOperator_equivariant ρ (b i) a x)
  · intro x hx
    have hz (i : ι) : T i =ᶠ[𝓝 x] 0 :=
      equivariantBumpOperator_eventually_zero_outside ρ (b i) W (hb i).2.2.1 hinv x hx
    filter_upwards [Filter.eventually_all.mpr hz] with y hy
    simp only [linearPerturbation, hy, Pi.zero_apply, zero_apply,
      Finset.sum_const_zero, add_zero]
  · intro x hx
    exact hp ⟨x, hx⟩
  · intro x hx hr
    rw [(linearPerturbation_hasFDerivAt f T (hf.differentiable (by norm_num) x)
      (fun i => (hT i).differentiable (by norm_num) x) p).fderiv]
    exact hreg x hx hr

end EquivariantRegularization
end EilenbergGanea
namespace EilenbergGanea
open Set Filter Topology
open scoped ContDiff
section MixedRegularization
variable {G A V : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V]

def scalarRotationRepresentation (χ : G →* ℂˣ) : G →* (A × V) ≃L[ℝ] (A × V) where
  toFun g := scalarRotation (χ g)
  map_one' := by
    apply ContinuousLinearEquiv.ext
    funext q
    change scalarRotation (χ 1) q = q
    simp [scalarRotation_apply]
  map_mul' g h := by
    apply ContinuousLinearEquiv.ext
    funext q
    change scalarRotation (χ (g * h)) q = scalarRotation (χ g) (scalarRotation (χ h) q)
    simp [mul_smul]

omit [Fintype G] [FiniteDimensional ℝ A] [FiniteDimensional ℂ V] in
@[simp] theorem scalarRotationRepresentation_apply (χ : G →* ℂˣ) (g : G) (q : A × V) :
    scalarRotationRepresentation χ g q = (q.1, (χ g : ℂ) • q.2) := rfl

omit [Fintype G] [FiniteDimensional ℝ A] [FiniteDimensional ℂ V] in
 theorem scalarRotation_free (χ : G →* ℂˣ) (hχ : Function.Injective χ)
    (q : A × V) (hq : q.2 ≠ 0) :
    ∀ g : G, scalarRotationRepresentation χ g q = q → g = 1 := by
  intro g hg
  have hh : (χ g : ℂ) • q.2 = (1 : ℂ) • q.2 := by
    have hg_snd := congrArg Prod.snd hg
    change (χ g : ℂ) • q.2 = q.2 at hg_snd
    simpa using hg_snd
  have he : (χ g : ℂ) = 1 := (smul_left_injective ℂ hq) hh
  apply hχ
  apply Units.ext
  simpa using he

omit [Fintype G] [FiniteDimensional ℝ A] [FiniteDimensional ℂ V] in
 theorem normalShift_equivariant (χ : G →* ℂˣ) (f : A × V → A × V)
    (hf : ∀ g q, f (scalarRotationRepresentation χ g q) =
      scalarRotationRepresentation χ g (f q)) (s : ℝ) :
    ∀ g q, normalShift f s (scalarRotationRepresentation χ g q) =
      scalarRotationRepresentation χ g (normalShift f s q) := by
  intro g q
  simp only [normalShift, hf, map_add, map_smul]
  congr 1

/-- The full fixed-plus-free regularization step in fixed/normal coordinates.
Unlike an assumed transversality interface, this is assembled from the finite
normal spectrum argument and explicit free-orbit bump parameters above. -/
theorem exists_fixed_free_regularization (χ : G →* ℂˣ) (hχ : Function.Injective χ)
    (a₀ : G) (ha₀ : (χ a₀ : ℂ).im ≠ 0)
    (f : A × V → A × V) (hf : ContDiff ℝ ∞ f)
    (he : ∀ g q, f (scalarRotationRepresentation χ g q) =
      scalarRotationRepresentation χ g (f q))
    (K : Set (A × V)) (hK : IsCompact K) (S : Finset A)
    (hS : ∀ a, (a, 0) ∈ K → f (a, 0) = 0 → a ∈ S)
    (c : ℝ) (hc : c ≠ 0)
    (hT : ∀ a ∈ S, (fderiv ℝ (fixedRestriction f) a).det = c)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : A × V → A × V, ContDiff ℝ ∞ g ∧
      (∀ a q, g (scalarRotationRepresentation χ a q) =
        scalarRotationRepresentation χ a (g q)) ∧
      (∀ a, g (a, 0) = f (a, 0)) ∧
      (∀ q ∈ K, ‖g q - f q‖ < ε) ∧
      (∀ q ∈ K, g q = 0 → (fderiv ℝ g q).det ≠ 0) ∧
      (∀ a ∈ S, (0 < (fderiv ℝ g (a, 0)).det ↔ 0 < c)) := by
  classical
  let : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  let : MeasurableSpace (A × V) := borel (A × V)
  let : BorelSpace (A × V) := ⟨rfl⟩
  let ρ := scalarRotationRepresentation (A := A) (V := V) χ
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_lt
  have hδ : 0 < (ε / 2) / (R + 1) := div_pos (by linarith) (by linarith)
  obtain ⟨s, hs, hreg⟩ := exists_normalShift_regular_fixed f
    (hf.differentiable (by simp)) (χ a₀) ha₀ (he a₀) S c hc hT _ hδ
  let f₁ := normalShift f s
  have hf₁ : ContDiff ℝ ∞ f₁ := normalShift_contDiff f hf s
  have he₁ : ∀ a q, f₁ (ρ a q) = ρ a (f₁ q) := normalShift_equivariant χ f he s
  have hsmall : ∀ q ∈ K, ‖f₁ q - f q‖ < ε / 2 := by
    intro q hq
    have hnorm : ‖normalProjection q‖ ≤ R + 1 := by
      simp only [normalProjection_apply, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
      exact (norm_snd_le q).trans (hbound q hq).le |>.trans (by linarith)
    calc
      ‖f₁ q - f q‖ = |s| * ‖normalProjection q‖ := by simp only [f₁, normalShift, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      _ ≤ |s| * (R + 1) := mul_le_mul_of_nonneg_left hnorm (abs_nonneg _)
      _ < ε / 2 := (lt_div_iff₀ (by linarith : 0 < R + 1)).mp hs
  let W : Set (A × V) := {q | q.2 ≠ 0}
  have hW : IsOpen W := (isClosed_singleton.preimage continuous_snd).isOpen_compl
  have hinv : ∀ a q, q ∈ W → ρ a q ∈ W := by
    intro a q hq
    exact smul_ne_zero (Units.ne_zero _) hq
  have hcritical : ∀ q ∈ K, f₁ q = 0 → (fderiv ℝ f₁ q).det = 0 →
      q ∈ W ∧ ∀ a : G, ρ a q = q → a = 1 := by
    intro q hq hr hd
    have hn : q.2 ≠ 0 := by
      intro hz
      have hqeq : q = (q.1, 0) := Prod.ext rfl hz
      rw [hqeq] at hq hr hd
      have ha : q.1 ∈ S := hS q.1 hq (by simpa [f₁] using hr)
      exact (hreg q.1 ha).1 hd
    exact ⟨hn, scalarRotation_free χ hχ q hn⟩
  obtain ⟨g, hg, hge, hprotected, hclose, hgood⟩ :=
    exists_equivariant_regular_perturbation ρ f₁ hf₁ he₁ K W hK hW hinv hcritical
      (ε / 2) (by linarith)
  refine ⟨g, hg, hge, ?_, ?_, hgood, ?_⟩
  · intro a
    exact ((hprotected (a, 0) (by simp [W])).eq_of_nhds).trans (normalShift_fixed f s a)
  · intro q hq
    have hh := norm_sub_le_norm_sub_add_norm_sub (g q) (f₁ q) (f q)
    linarith [hclose q hq, hsmall q hq]
  · intro a ha
    have hd := (hprotected (a, 0) (by simp [W])).fderiv_eq (𝕜 := ℝ)
    rw [hd]
    exact (hreg a ha).2

end MixedRegularization
end EilenbergGanea


namespace EilenbergGanea
section SignedAction
variable {G X : Type*} [Group G] [MulAction G X]

@[instance_reducible] def invariantSubtypeAction (P : X → Prop) (hP : ∀ (g : G) x, P x → P (g • x)) :
    MulAction G {x // P x} where
  smul g x := ⟨g • x.1, hP g x.1 x.2⟩
  one_smul x := Subtype.ext (one_smul G x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

theorem signed_finite_action_nonzero {p : ℕ} [Fact p.Prime] [Fintype X]
    (hG : IsPGroup p G) (σ : X → Bool)
    (hσ : ∀ (g : G) x, σ (g • x) = σ x)
    (b : Bool) (hb : ∀ x ∈ MulAction.fixedPoints G X, σ x = b)
    (hex : (MulAction.fixedPoints G X).Nonempty)
    (hsmall : Nat.card (MulAction.fixedPoints G X) < p) :
    (∑ x : X, (if σ x then (1 : ℤ) else -1)) ≠ 0 := by
  classical
  let A := {x : X // σ x = b}
  let B := {x : X // σ x ≠ b}
  let : MulAction G A := invariantSubtypeAction _ (by intro g x hx; simpa [hσ] using hx)
  let : MulAction G B := invariantSubtypeAction _ (by intro g x hx; simpa [hσ] using hx)
  let e : MulAction.fixedPoints G A ≃ MulAction.fixedPoints G X :=
    { toFun := fun x => ⟨x.1.1, fun g => congrArg Subtype.val (x.2 g)⟩
      invFun := fun x => ⟨⟨x.1, hb x.1 x.2⟩, fun g => Subtype.ext (x.2 g)⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  have hempty : IsEmpty (MulAction.fixedPoints G B) := ⟨by
    intro x
    have hx : x.1.1 ∈ MulAction.fixedPoints G X := fun g => congrArg Subtype.val (x.2 g)
    exact x.1.2 (hb x.1.1 hx)⟩
  have hnon : Nonempty (MulAction.fixedPoints G X) := hex.to_subtype
  have hpos : 0 < Nat.card (MulAction.fixedPoints G A) := by
    rw [Nat.card_congr e]
    exact Nat.card_pos
  have hs : Nat.card (MulAction.fixedPoints G A) < p := by rw [Nat.card_congr e]; exact hsmall
  have hn : Nat.card (MulAction.fixedPoints G B) = 0 := by simp
  have hneq : Nat.card A ≠ Nat.card B := by
    intro hh
    have h := (hG.card_modEq_card_fixedPoints A).symm
    rw [hh] at h
    have h' := h.trans (hG.card_modEq_card_fixedPoints B)
    rw [hn] at h'
    have heq := h'.eq_of_lt_of_lt hs (Fact.out : p.Prime).pos
    omega
  have hcounts : (∑ x : X, (if σ x = b then (1 : ℤ) else -1)) =
      (Nat.card A : ℤ) - Nat.card B := by
    rw [Finset.sum_ite]
    simp [A, B, Nat.card_eq_fintype_card, Fintype.card_subtype, sub_eq_add_neg]
  intro hz
  have hz' : (∑ x : X, (if σ x = b then (1 : ℤ) else -1)) = 0 := by
    cases b
    · have hh : (fun x : X => if σ x = false then (1 : ℤ) else -1) =
          fun x => -(if σ x then (1 : ℤ) else -1) := by funext x; cases σ x <;> rfl
      rw [hh, Finset.sum_neg_distrib, hz, neg_zero]
    · simpa using hz
  rw [hcounts, sub_eq_zero] at hz'
  exact hneq (by exact_mod_cast hz')
end SignedAction
end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/- A nonsingular derivative supplies an open inverse patch, without assuming
that the map is proper or globally injective. -/
theorem exists_regular_inverse_patch (f : E → E) {x : E}
    (hf : ContDiffAt ℝ 1 f x) (hd : (fderiv ℝ f x).det ≠ 0) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ InjOn f V ∧
      IsOpen (f '' V) := by
  let e := (fderiv ℝ f x).toContinuousLinearEquivOfDetNeZero hd
  have he : (e : E →L[ℝ] E) = fderiv ℝ f x := rfl
  have hf' : HasFDerivAt f (e : E →L[ℝ] E) x := by
    rw [he]
    exact (hf.differentiableAt (by norm_num)).hasFDerivAt
  let p := hf.toOpenPartialHomeomorph f hf' (by norm_num)
  refine ⟨p.source, p.open_source, hf.mem_toOpenPartialHomeomorph_source hf' (by norm_num),
    p.injOn, ?_⟩
  change IsOpen (p '' p.source)
  rw [p.image_source_eq_target]
  exact p.open_target

/- A regular level set is discrete. Only smoothness at the level set is
required. -/
theorem regular_fiber_isDiscrete (f : E → E) (y : E) (K : Set E)
    (hf : ∀ x ∈ K, f x = y → ContDiffAt ℝ 1 f x)
    (hd : ∀ x ∈ K, f x = y → (fderiv ℝ f x).det ≠ 0) :
    IsDiscrete (K ∩ f ⁻¹' {y}) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  rintro x ⟨hxK, hxy⟩
  obtain ⟨V, ho, hxV, hi, _⟩ := exists_regular_inverse_patch f (hf x hxK hxy) (hd x hxK hxy)
  refine ⟨V, ho, ?_⟩
  ext z
  constructor
  · rintro ⟨hzV, hzK, hzy⟩
    exact hi hzV hxV (hzy.trans hxy.symm)
  · rintro rfl
    exact ⟨hxV, hxK, hxy⟩

/- Compact regular fibers are finite, in the form needed by the signed
count formula after regularization. -/
theorem compact_regular_fiber_finite (f : E → E) (y : E) (K : Set E)
    (hK : IsCompact K) (hf : ContinuousOn f K)
    (hs : ∀ x ∈ K, f x = y → ContDiffAt ℝ 1 f x)
    (hd : ∀ x ∈ K, f x = y → (fderiv ℝ f x).det ≠ 0) :
    (K ∩ f ⁻¹' {y}).Finite := by
  exact (hK.of_isClosed_subset (hf.preimage_isClosed_of_isClosed hK.isClosed
    isClosed_singleton) inter_subset_left).finite
    (regular_fiber_isDiscrete f y K hs hd)


end EilenbergGanea
namespace EilenbergGanea
open Set Filter Topology
open scoped ContDiff
section LocalizedRegularization
variable {G A V : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V]

/-- The localized noncancellation part of degree, now for actual regular
perturbations of a smooth map, not an assumed finite-orbit-count interface. -/
theorem exists_regularization_nonzero_count {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) (χ : G →* ℂˣ) (hχ : Function.Injective χ)
    (a₀ : G) (ha₀ : (χ a₀ : ℂ).im ≠ 0)
    (f : A × V → A × V) (hf : ContDiff ℝ ∞ f)
    (he : ∀ a q, f (scalarRotationRepresentation χ a q) =
      scalarRotationRepresentation χ a (f q))
    (K : Set (A × V)) (hK : IsCompact K)
    (hKi : ∀ a q, q ∈ K → scalarRotationRepresentation χ a q ∈ K)
    (L : Set (A × V)) (hL : IsCompact L) (hKL : K ⊆ L)
    (S : Finset A) (hS : ∀ a, (a, 0) ∈ L → f (a, 0) = 0 → a ∈ S)
    (hex : ∃ a, (a, 0) ∈ K ∧ f (a, 0) = 0) (hSp : S.card < p)
    (c : ℝ) (hc : c ≠ 0)
    (hT : ∀ a ∈ S, (fderiv ℝ (fixedRestriction f) a).det = c)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : A × V → A × V, ContDiff ℝ ∞ g ∧
      (∀ q ∈ L, ‖g q - f q‖ < ε) ∧
      ∃ s : Finset (A × V), (∀ q, q ∈ s ↔ q ∈ K ∧ g q = 0) ∧
        (∀ q ∈ s, (fderiv ℝ g q).det ≠ 0) ∧
        (∑ q ∈ s, (if 0 < (fderiv ℝ g q).det then 1 else -1 : ℝ)) ≠ 0 := by
  classical
  let : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  let ρ := scalarRotationRepresentation (A := A) (V := V) χ
  obtain ⟨g, hg, hge, hgf, hclose, hreg, hsign⟩ := exists_fixed_free_regularization
    χ hχ a₀ ha₀ f hf he L hL S hS c hc hT ε hε
  have hfinite : (K ∩ g ⁻¹' {0}).Finite := compact_regular_fiber_finite g 0 K hK
    hg.continuous.continuousOn (fun q _ _ => hg.of_le (by norm_num) |>.contDiffAt) (fun q hq => hreg q (hKL hq))
  let s := hfinite.toFinset
  have hs : ∀ q, q ∈ s ↔ q ∈ K ∧ g q = 0 := by intro q; exact hfinite.mem_toFinset
  let X := {q : A × V // q ∈ K ∧ g q = 0}
  let : Fintype X := hfinite.fintype
  let : MulAction G (A × V) := {
    smul := fun a q => ρ a q
    one_smul := by intro q; change ρ 1 q = q; rw [map_one]; rfl
    mul_smul := by intro a b q; change ρ (a * b) q = ρ a (ρ b q); rw [map_mul]; rfl }
  let : MulAction G X := invariantSubtypeAction _ (by
    intro a q hq
    refine ⟨hKi a q hq.1, ?_⟩
    change g (ρ a q) = 0
    rw [hge, hq.2, map_zero])
  have hfixed (x : MulAction.fixedPoints G X) : x.1.1.2 = 0 := by
    by_contra hn
    have hh := congrArg (fun q : X => q.1.2) (x.2 a₀)
    change (χ a₀ : ℂ) • x.1.1.2 = x.1.1.2 at hh
    have hh' : (χ a₀ : ℂ) • x.1.1.2 = (1 : ℂ) • x.1.1.2 := by simpa using hh
    have heq := (smul_left_injective ℂ hn) hh'
    exact ha₀ (by rw [heq]; rfl)
  have hmem (x : MulAction.fixedPoints G X) : x.1.1.1 ∈ S := by
    have hx := x.1.2
    have heq : x.1.1 = (x.1.1.1, 0) := Prod.ext rfl (hfixed x)
    rw [heq] at hx
    exact hS _ (hKL hx.1) (by rw [← hgf]; exact hx.2)
  let e : MulAction.fixedPoints G X ↪ S :=
    ⟨fun x => ⟨x.1.1.1, hmem x⟩, by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg Subtype.val h
      · exact (hfixed x).trans (hfixed y).symm⟩
  have hsmall : Nat.card (MulAction.fixedPoints G X) < p :=
    (Nat.card_le_card_of_injective e e.injective).trans_lt (by simpa using hSp)
  have hex' : (MulAction.fixedPoints G X).Nonempty := by
    obtain ⟨a, haK, haf⟩ := hex
    refine ⟨⟨(a, 0), haK, by rw [hgf]; exact haf⟩, ?_⟩
    intro b
    apply Subtype.ext
    change ρ b (a, 0) = (a, 0)
    simp [ρ]
  let σ : X → Bool := fun q => decide (0 < (fderiv ℝ g q.1).det)
  have hσ : ∀ (a : G) (q : X), σ (a • q) = σ q := by
    intro a q
    unfold σ
    congr 1
    exact congrArg (fun t : ℝ => 0 < t)
      (equivariant_fderiv_det g (ρ a) (hg.differentiable (by simp)) (hge a) q.1)
  have hb : ∀ q ∈ MulAction.fixedPoints G X, σ q = decide (0 < c) := by
    intro q hq
    let x : MulAction.fixedPoints G X := ⟨q, hq⟩
    have heq : q.1 = (q.1.1, 0) := Prod.ext rfl (hfixed x)
    change decide (0 < (fderiv ℝ g q.1).det) = decide (0 < c)
    rw [heq]
    exact decide_eq_decide.mpr (hsign _ (hmem x))
  have hcount := signed_finite_action_nonzero hG σ hσ (decide (0 < c)) hb hex' hsmall
  refine ⟨g, hg, hclose, s, hs, fun q hq => hreg q (hKL ((hs q).mp hq).1) ((hs q).mp hq).2, ?_⟩
  have hsum : (∑ q ∈ s, (if 0 < (fderiv ℝ g q).det then (1 : ℤ) else -1)) ≠ 0 := by
    have hsum' : (∑ q : X, (if σ q then (1 : ℤ) else -1)) =
        ∑ q ∈ s, (if 0 < (fderiv ℝ g q).det then (1 : ℤ) else -1) := by
      unfold σ
      simpa only [decide_eq_true_eq] using (Finset.sum_subtype s hs
        (fun q => if 0 < (fderiv ℝ g q).det then (1 : ℤ) else -1)).symm
    exact hsum' ▸ hcount
  exact_mod_cast hsum
end LocalizedRegularization
end EilenbergGanea


end

end OAI
