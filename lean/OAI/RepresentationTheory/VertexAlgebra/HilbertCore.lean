import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.ConstrainedSquareBound

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
open Filter
namespace HilbertCore
open UniformSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
def space (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] :
    Submodule ℂ (Completion V) :=
  LinearMap.range (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap

def equiv (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] :
    V ≃ₗ[ℂ] space V :=
  LinearEquiv.ofInjective (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap
    (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).injective

@[simp] theorem equiv_coe (v : V) : (equiv V v : Completion V) = (v : Completion V) := rfl
@[simp] theorem equiv_symm_coe (v : space V) :
    ((equiv V).symm v : Completion V) = (v : Completion V) :=
  LinearEquiv.ofInjective_symm_apply _ v

theorem dense : Dense (space V : Set (Completion V)) := by
  change Dense (Set.range (fun v : V => (v : Completion V)))
  exact Completion.denseRange_coe

 
def operator (T : V →ₗ[ℂ] Completion V) : Completion V →ₗ.[ℂ] Completion V where
  domain := space V
  toFun := T.comp (equiv V).symm.toLinearMap

@[simp] theorem operator_apply (T : V →ₗ[ℂ] Completion V) (v : V) :
    operator T (equiv V v) = T v := by simp [operator]

theorem formalAdjoint {T S : V →ₗ[ℂ] Completion V}
    (h : ∀ v w : V, inner ℂ (T v) (w : Completion V) =
      inner ℂ (v : Completion V) (S w)) :
    (operator T).IsFormalAdjoint (operator S) := by
  intro v w
  obtain ⟨v, rfl⟩ := (equiv V).surjective v
  obtain ⟨w, rfl⟩ := (equiv V).surjective w
  simpa using h v w

 

theorem closable {T S : V →ₗ[ℂ] Completion V}
    (h : ∀ v w : V, inner ℂ (T v) (w : Completion V) =
      inner ℂ (v : Completion V) (S w)) : (operator T).IsClosable := by
  have H := formalAdjoint h
  exact ((operator S).adjoint_isClosed dense).isClosable.leIsClosable (H.symm.le_adjoint dense)

end HilbertCore

 

def RapidCoefficients (f : ℤ → ℂ) : Prop :=
  ∀ p : ℕ, Summable (fun n : ℤ => ‖f n‖*(1+|(n : ℝ)|)^p)

namespace RapidCoefficients
variable {f g : ℤ → ℂ}

theorem conj (h : RapidCoefficients f) : RapidCoefficients (fun n => star (f n)) := by
  intro p
  simpa only [norm_star] using h p

theorem neg_index (h : RapidCoefficients f) : RapidCoefficients (fun n => f (-n)) := by
  intro p
  simpa only [Function.comp_def, Equiv.neg_apply, Int.cast_neg, abs_neg] using
    (Equiv.neg ℤ).summable_iff.mpr (h p)

theorem add (hf : RapidCoefficients f) (hg : RapidCoefficients g) :
    RapidCoefficients (fun n => f n + g n) := by
  intro p
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ ((hf p).add (hg p))
  intro n
  calc
    _ ≤ (‖f n‖+‖g n‖)*(1+|(n : ℝ)|)^p := mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
    _ = _ := by ring

theorem smul (hf : RapidCoefficients f) (z : ℂ) : RapidCoefficients (fun n => z * f n) := by
  intro p
  simpa only [norm_mul, mul_assoc] using (hf p).mul_left ‖z‖

theorem summable_norm_smul {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup H] [NormedSpace ℂ H] (hf : RapidCoefficients f)
    (T : ℤ → V →ₗ[ℂ] H) {C K : ℝ} {p : ℕ}
    (v : V) (hT : ∀ n, ‖T n v‖ ≤ C*(1+|(n : ℝ)|)^p*K) :
    Summable (fun n => ‖f n • T n v‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ((hf p).mul_right (C*K))
  intro n
  rw [norm_smul]
  calc
    _ ≤ ‖f n‖*(C*(1+|(n : ℝ)|)^p*K) := mul_le_mul_of_nonneg_left (hT n) (norm_nonneg _)
    _ = _ := by ring

end RapidCoefficients

namespace SummableLinearFamily
section
variable {ι V H : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup H] [NormedSpace ℂ H]

def tsumMap (T : ι → V →ₗ[ℂ] H) (hT : ∀ v, Summable (fun n => T n v)) : V →ₗ[ℂ] H where
  toFun v := ∑' n, T n v
  map_add' v w := by simpa only [map_add] using (hT v).tsum_add (hT w)
  map_smul' z v := by
    simpa only [map_smul, RingHom.id_apply] using (hT v).tsum_const_smul z

end
variable {ι V H : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem adjoint_tsum {T S : ι → V →ₗ[ℂ] H} (hT : ∀ v, Summable (fun n => T n v))
    (hS : ∀ v, Summable (fun n => S n v)) (j : V →ₗ[ℂ] H)
    (Hadj : ∀ n v w, inner ℂ (T n v) (j w) = inner ℂ (j v) (S n w)) (v w : V) :
    inner ℂ (tsumMap T hT v) (j w) = inner ℂ (j v) (tsumMap S hS w) := by
  change inner ℂ (∑' n, T n v) (j w) = inner ℂ (j v) (∑' n, S n w)
  calc
    _ = ∑' n, inner ℂ (T n v) (j w) := ((innerSL ℂ).flip (j w)).map_tsum (hT v)
    _ = ∑' n, inner ℂ (j v) (S n w) := tsum_congr (fun n => Hadj n v w)
    _ = _ := ((innerSL ℂ (j v)).map_tsum (hS w)).symm

end SummableLinearFamily

namespace CFTTypeVOA
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

 

theorem PolynomialEnergyBound.physical {a : V} (ha : A.PolynomialEnergyBound a) (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ p k : ℕ, ∀ m v,
      ‖A.physicalMode a d m v‖ ≤ C*(1+|(m : ℝ)|)^p*‖(A.energyShift^k) v‖ := by
  obtain ⟨C, hC, p, k, H⟩ := ha
  refine ⟨C*(1+|((d : ℝ)-1)|)^p, by positivity, p, k, ?_⟩
  intro m v
  apply (H (m+d-1) v).trans
  have he : 1+|((m+(d : ℤ)-1 : ℤ) : ℝ)| ≤ (1+|((d : ℝ)-1)|)*(1+|(m : ℝ)|) := by
    have ht := abs_add_le (m : ℝ) ((d : ℝ)-1)
    have hn := mul_nonneg (abs_nonneg ((d : ℝ)-1)) (abs_nonneg (m : ℝ))
    push_cast
    rw [add_sub_assoc]
    nlinarith
  calc
    _ ≤ C*((1+|((d : ℝ)-1)|)*(1+|(m : ℝ)|))^p*‖(A.energyShift^k) v‖ := by gcongr
    _ = _ := by rw [mul_pow]; ring

 
theorem summable_norm_physicalSmear {a : V} (ha : A.PolynomialEnergyBound a)
    (d : ℕ) {f : ℤ → ℂ} (hf : RapidCoefficients f) (v : V) :
    Summable (fun m : ℤ => ‖f m • (A.physicalMode a d m v : Completion V)‖) := by
  obtain ⟨C, _, p, k, H⟩ := ha.physical A d
  apply hf.summable_norm_smul
    (fun m => (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap.comp (A.physicalMode a d m))
    v (C := C) (K := ‖(A.energyShift^k) v‖) (p := p)
  intro m
  simpa only [LinearMap.comp_apply, LinearIsometry.coe_toLinearMap, LinearIsometry.norm_map] using H m v

 
def smearedMap (a : V) (d : ℕ) (ha : A.PolynomialEnergyBound a)
    (f : ℤ → ℂ) (hf : RapidCoefficients f) : V →ₗ[ℂ] Completion V :=
  SummableLinearFamily.tsumMap
    (fun m => f m • (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap.comp
      (A.physicalMode a d m))
    (fun v => (A.summable_norm_physicalSmear ha d hf v).of_norm)

@[simp] theorem smearedMap_apply (a : V) (d : ℕ) (ha : A.PolynomialEnergyBound a)
    (f : ℤ → ℂ) (hf : RapidCoefficients f) (v : V) :
    A.smearedMap a d ha f hf v = ∑' m : ℤ, f m • (A.physicalMode a d m v : Completion V) := rfl

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)

 

theorem summable_adjointPhysicalSmear (hc : A.toVertexAlgebra.C2Cofinite)
    (a : V) (d : ℕ) {f : ℤ → ℂ} (hf : RapidCoefficients f) (v : V) :
    Summable (fun m : ℤ => star (f m) • (U.adjointPhysicalMode a d m v : Completion V)) := by
  have hs (j : ℕ) : Summable (fun m : ℤ =>
      star (f m) • (A.physicalMode ((A.virasoroMode 1^j) (U.pct a)) (d-j) (-m) v : Completion V)) := by
    have h := (A.summable_norm_physicalSmear
      (U.polynomialEnergyBounds hc ((A.virasoroMode 1^j) (U.pct a))) (d-j)
      hf.conj.neg_index v).of_norm
    simpa only [Function.comp_def, Equiv.neg_apply, neg_neg] using
      (Equiv.neg ℤ).summable_iff.mpr h
  have hs' (j : ℕ) := (hs j).const_smul ((-1 : ℂ)^d * (j.factorial : ℂ)⁻¹)
  have H := summable_sum (s := Finset.range (d+1)) (fun j _ => hs' j)
  convert H using 1
  ext m
  change star (f m) • (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) (U.adjointPhysicalMode a d m v) = _
  simp only [adjointPhysicalMode, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  ring

 
theorem smearedCore_closable (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    (HilbertCore.operator (A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf)).IsClosable := by
  let j : V →ₗ[ℂ] Completion V := (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap
  let T (m : ℤ) : V →ₗ[ℂ] Completion V := f m • j.comp (A.physicalMode a d m)
  let S (m : ℤ) : V →ₗ[ℂ] Completion V := star (f m) • j.comp (U.adjointPhysicalMode a d m)
  have hT : ∀ v, Summable (fun m => T m v) := fun v =>
    (A.summable_norm_physicalSmear (U.polynomialEnergyBounds hc a) d hf v).of_norm
  have hS : ∀ v, Summable (fun m => S m v) := fun v => U.summable_adjointPhysicalSmear hc a d hf v
  have Hadj (m : ℤ) (x y : V) : inner ℂ (T m x) (j y) = inner ℂ (j x) (S m y) := by
    change inner ℂ (f m • (A.physicalMode a d m x : Completion V)) (y : Completion V) =
      inner ℂ (x : Completion V) (star (f m) • (U.adjointPhysicalMode a d m y : Completion V))
    simp only [inner_smul_left, inner_smul_right, Completion.inner_coe]
    rw [U.adjointPhysicalMode_inner ha]
    rfl
  exact HilbertCore.closable (SummableLinearFamily.adjoint_tsum hT hS j Hadj)

 

def closedSmearedOperator (hc : A.toVertexAlgebra.C2Cofinite)
    (a : V) (d : ℕ) (f : ℤ → ℂ) (hf : RapidCoefficients f) :
    Completion V →ₗ.[ℂ] Completion V :=
  (HilbertCore.operator (A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf)).closure

theorem closedSmearedOperator_isClosed (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    (U.closedSmearedOperator hc a d f hf).IsClosed :=
  (U.smearedCore_closable hc ha hf).closure_isClosed

end UnitaryStructure
end CFTTypeVOA

open scoped ContDiff

 

structure SmoothCircleFunction where
  toFun : ℝ → ℂ
  periodic : Function.Periodic toFun (2*Real.pi)
  smooth : ContDiff ℝ ∞ toFun

namespace SmoothCircleFunction
instance : CoeFun SmoothCircleFunction (fun _ => ℝ → ℂ) := ⟨toFun⟩

theorem period_pos : 0 < 2*Real.pi := by positivity

def coefficient (f : SmoothCircleFunction) (n : ℤ) : ℂ :=
  fourierCoeffOn period_pos f n

theorem periodic_iteratedDeriv (f : SmoothCircleFunction) (k : ℕ) :
    Function.Periodic (iteratedDeriv k f) (2*Real.pi) := by
  intro x
  have he : (fun y => f (y+2*Real.pi)) = f := funext f.periodic
  have h := congrFun (iteratedDeriv_comp_add_const k (f : ℝ → ℂ) (2*Real.pi)) x
  rw [he] at h
  exact h.symm

theorem continuous_iteratedDeriv (f : SmoothCircleFunction) (k : ℕ) :
    Continuous (iteratedDeriv k f) := f.smooth.continuous_iteratedDeriv k (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))

theorem differentiable_iteratedDeriv (f : SmoothCircleFunction) (k : ℕ) :
    Differentiable ℝ (iteratedDeriv k f) := f.smooth.differentiable_iteratedDeriv k (by exact_mod_cast ENat.natCast_lt_top k)

 

theorem coefficient_deriv_step (f : SmoothCircleFunction) (k : ℕ) {n : ℤ} (hn : n ≠ 0) :
    (Complex.I*(n : ℂ))*fourierCoeffOn period_pos (iteratedDeriv k f) n =
      fourierCoeffOn period_pos (iteratedDeriv (k+1) f) n := by
  have HD (x : ℝ) : HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k+1) f x) x := by
    rw [iteratedDeriv_succ]
    exact (f.differentiable_iteratedDeriv k x).hasDerivAt
  have H := fourierCoeffOn_of_hasDerivAt period_pos hn (fun x _ => HD x)
    ((f.continuous_iteratedDeriv (k+1)).intervalIntegrable 0 (2*Real.pi))
  have hp := f.periodic_iteratedDeriv k 0
  simp only [zero_add] at hp
  rw [hp, sub_self, mul_zero, zero_sub] at H
  rw [H]
  push_cast
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hn', hpi]
  ring

theorem coefficient_iteratedDeriv (f : SmoothCircleFunction) (k : ℕ) {n : ℤ} (hn : n ≠ 0) :
    (Complex.I*(n : ℂ))^k*f.coefficient n =
      fourierCoeffOn period_pos (iteratedDeriv k f) n := by
  induction k with
  | zero => simp [coefficient]
  | succ k ih =>
    rw [pow_succ', mul_assoc, ih]
    exact f.coefficient_deriv_step k hn

 

theorem coefficient_norm_le {g : ℝ → ℂ} {C : ℝ}
    (hC : ∀ x ∈ Set.Icc 0 (2*Real.pi), ‖g x‖ ≤ C) (n : ℤ) :
    ‖fourierCoeffOn period_pos g n‖ ≤ C := by
  rw [fourierCoeffOn_eq_integral, norm_smul]
  have H : ‖∫ x in (0 : ℝ)..2*Real.pi,
      fourier (-n) (x : AddCircle (2*Real.pi-0)) • g x‖ ≤ C*|2*Real.pi-0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [norm_smul, show ‖fourier (-n) (x : AddCircle (2*Real.pi-0))‖ = 1 from Circle.norm_coe _, one_mul]
    exact hC x (by
      rw [Set.uIoc_of_le period_pos.le] at hx
      exact ⟨hx.1.le, hx.2⟩)
  calc
    _ ≤ ‖(1 / (2*Real.pi-0) : ℝ)‖*(C*|2*Real.pi-0|) := mul_le_mul_of_nonneg_left H (norm_nonneg _)
    _ = C := by
      rw [sub_zero, Real.norm_eq_abs, abs_of_pos (by positivity), abs_of_pos period_pos]
      field_simp

 
theorem coefficient_polynomial_decay (f : SmoothCircleFunction) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ, n ≠ 0 → |(n : ℝ)|^k * ‖f.coefficient n‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f.continuous_iteratedDeriv k).continuousOn (s := Set.Icc 0 (2*Real.pi))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, period_pos.le⟩)
  refine ⟨C, hC0, ?_⟩
  intro n hn
  have H := congrArg norm (f.coefficient_iteratedDeriv k hn)
  have hn' : ‖(n : ℂ)‖ = |(n : ℝ)| := by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
  simp only [norm_mul, norm_pow, Complex.norm_I, one_mul, hn'] at H
  rw [H]
  exact coefficient_norm_le hC n

 

theorem rapid_coefficients (f : SmoothCircleFunction) : RapidCoefficients f.coefficient := by
  intro p
  obtain ⟨C, hC, HC⟩ := f.coefficient_polynomial_decay (p+2)
  have hweight {x r : ℝ} (hx : 1 ≤ x) (hr : 0 ≤ r) (H : x^(p+2)*r ≤ C) :
      r*(1+x)^p ≤ (2^p*C)*(x^2)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one hx) _)).mpr
    calc
      _ ≤ r*(2*x)^p*x^2 := by gcongr; linarith
      _ = 2^p*(x^(p+2)*r) := by rw [pow_add, mul_pow]; ring
      _ ≤ 2^p*C := mul_le_mul_of_nonneg_left H (by positivity)
  have hs : Summable (fun n : ℕ => (2^p*C)*(((n+1 : ℕ) : ℝ)^2)⁻¹) :=
    ((summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2))).mul_left _
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · apply (summable_nat_add_iff 1).mp
    apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hs
    intro n
    have hn : ((n+1 : ℕ) : ℤ) ≠ 0 := by omega
    have hx : 1 ≤ |(((n+1 : ℕ) : ℤ) : ℝ)| := by
      rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast Nat.succ_pos n
    have H := hweight hx (norm_nonneg (f.coefficient ((n+1 : ℕ) : ℤ))) (HC _ hn)
    simpa only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (n+1))] using H
  · apply (summable_nat_add_iff 1).mp
    apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hs
    intro n
    have hn : -((n+1 : ℕ) : ℤ) ≠ 0 := by omega
    have hx : 1 ≤ |((-((n+1 : ℕ) : ℤ) : ℤ) : ℝ)| := by
      rw [Int.cast_neg, abs_neg, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast Nat.succ_pos n
    have H := hweight hx (norm_nonneg (f.coefficient (-((n+1 : ℕ) : ℤ)))) (HC _ hn)
    simpa only [Int.cast_neg, abs_neg, Int.cast_natCast,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (n+1))] using H

end SmoothCircleFunction

namespace CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {A : CFTTypeVOA V} (U : A.UnitaryStructure)

 

def smoothSmearedField (hc : A.toVertexAlgebra.C2Cofinite)
    (a : V) (d : ℕ) (f : SmoothCircleFunction) : Completion V →ₗ.[ℂ] Completion V :=
  HilbertCore.operator (A.smearedMap a d (U.polynomialEnergyBounds hc a)
    f.coefficient f.rapid_coefficients)

theorem smoothSmearedField_closable (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (f : SmoothCircleFunction) :
    (U.smoothSmearedField hc a d f).IsClosable :=
  U.smearedCore_closable hc ha f.rapid_coefficients

 
def closedSmoothField (hc : A.toVertexAlgebra.C2Cofinite)
    (a : V) (d : ℕ) (f : SmoothCircleFunction) : Completion V →ₗ.[ℂ] Completion V :=
  (U.smoothSmearedField hc a d f).closure

theorem closedSmoothField_isClosed (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (f : SmoothCircleFunction) :
    (U.closedSmoothField hc a d f).IsClosed :=
  (U.smoothSmearedField_closable hc ha f).closure_isClosed

theorem closedSmoothField_graph (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (f : SmoothCircleFunction) :
    ((U.closedSmoothField hc a d f).graph : Set (Completion V × Completion V)) =
      closure ((U.smoothSmearedField hc a d f).graph : Set (Completion V × Completion V)) := by
  symm
  exact congrArg (fun S : Submodule ℂ (Completion V × Completion V) => (S : Set (Completion V × Completion V)))
    (U.smoothSmearedField_closable hc ha f).graph_closure_eq_closure_graph

end CFTTypeVOA.UnitaryStructure

section GraphData
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace ClosedGraphData

abbrev Double (H : Type u) := WithLp 2 (H × H)

 
def graph (T : H →ₗ.[ℂ] H) : Submodule ℂ (Double H) :=
  T.graph.comap (WithLp.prodContinuousLinearEquiv 2 ℂ H H).toLinearEquiv.toLinearMap

omit [CompleteSpace H] in
theorem graph_closed {T : H →ₗ.[ℂ] H} (hT : T.IsClosed) :
    IsClosed (graph T : Set (Double H)) :=
  hT.preimage (WithLp.prodContinuousLinearEquiv 2 ℂ H H).continuous

 

def projection (T : H →ₗ.[ℂ] H) (hT : T.IsClosed) : Double H →L[ℂ] Double H := by
  letI : IsClosed (graph T : Set (Double H)) := graph_closed hT
  exact (graph T).starProjection

def inclusion (i : Bool) : H →L[ℂ] Double H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap.comp
    (if i then ContinuousLinearMap.inr ℂ H H else ContinuousLinearMap.inl ℂ H H)

def coordinate (i : Bool) : Double H →L[ℂ] H :=
  (if i then ContinuousLinearMap.snd ℂ H H else ContinuousLinearMap.fst ℂ H H).comp
    (WithLp.prodContinuousLinearEquiv 2 ℂ H H).toContinuousLinearMap

 
def entry (T : H →ₗ.[ℂ] H) (hT : T.IsClosed) (i j : Bool) : H →L[ℂ] H :=
  (coordinate i).comp ((projection T hT).comp (inclusion j))

theorem projection_selfAdjoint (T : H →ₗ.[ℂ] H) (hT : T.IsClosed) :
    IsSelfAdjoint (projection T hT) := by
  let : IsClosed (graph T : Set (Double H)) := graph_closed hT
  exact isSelfAdjoint_starProjection (graph T)

theorem coordinate_eq_adjoint (i : Bool) :
    coordinate (H := H) i = (inclusion i).adjoint := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  cases i <;> simp [coordinate, inclusion, WithLp.prod_inner_apply]

theorem adjoint_inclusion (i : Bool) : (inclusion (H := H) i).adjoint = coordinate i :=
  (coordinate_eq_adjoint i).symm

theorem adjoint_coordinate (i : Bool) : (coordinate (H := H) i).adjoint = inclusion i := by
  rw [coordinate_eq_adjoint, ContinuousLinearMap.adjoint_adjoint]

 
theorem star_entry (T : H →ₗ.[ℂ] H) (hT : T.IsClosed) (i j : Bool) :
    star (entry T hT i j) = entry T hT j i := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  simp only [entry, ContinuousLinearMap.adjoint_comp, adjoint_inclusion,
    adjoint_coordinate, (projection_selfAdjoint T hT).adjoint_eq,
    ContinuousLinearMap.comp_assoc]

 
def diagonalAction (Q : H →L[ℂ] H) : Double H →L[ℂ] Double H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap.comp
    ((Q.prodMap Q).comp (WithLp.prodContinuousLinearEquiv 2 ℂ H H).toContinuousLinearMap)

theorem diagonalAction_adj (Q : H →L[ℂ] H) :
    (diagonalAction Q).adjoint = diagonalAction Q.adjoint := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  change inner ℂ (WithLp.toLp 2 (Q.adjoint x.ofLp.1, Q.adjoint x.ofLp.2)) y =
    inner ℂ x (WithLp.toLp 2 (Q y.ofLp.1, Q y.ofLp.2))
  simp only [WithLp.prod_inner_apply,
    ContinuousLinearMap.adjoint_inner_left]

omit [CompleteSpace H] in
theorem coordinate_diagonalAction (Q : H →L[ℂ] H) (i : Bool) :
    (coordinate i).comp (diagonalAction Q) = Q.comp (coordinate i) := by
  ext x
  cases i <;> simp [coordinate, diagonalAction]

omit [CompleteSpace H] in
theorem diagonalAction_inclusion (Q : H →L[ℂ] H) (i : Bool) :
    (diagonalAction Q).comp (inclusion i) = (inclusion i).comp Q := by
  ext x
  cases i <;> simp [inclusion, diagonalAction]

 

theorem commutes_projection_of_reduces (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (Q : H →L[ℂ] H) (hQ : ∀ x ∈ S, Q x ∈ S)
    (hQa : ∀ x ∈ S, Q.adjoint x ∈ S) :
    Q.comp S.starProjection = S.starProjection.comp Q := by
  ext x
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact hQ _ (S.starProjection_apply_mem x)
  · change Q x - Q (S.starProjection x) ∈ Sᗮ
    rw [← map_sub]
    apply (S.mem_orthogonal' _).mpr
    intro y hy
    rw [← ContinuousLinearMap.adjoint_inner_right]
    exact (S.mem_orthogonal' _).mp (Submodule.sub_starProjection_mem_orthogonal x)
      _ (hQa y hy)
end ClosedGraphData
end GraphData
end StronglyRationalVOA

end

end OAI
