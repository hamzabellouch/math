import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.StressSmoothness

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma smoothEnergyPower_zero (x : U.smoothEnergySpace) : U.smoothEnergyPower 0 x=(x:Completion V) := by
  have h := U.inverseSobolev_smoothEnergyPower 0 x
  rwa [U.inverseSobolev_zero,one_apply_eq_self] at h
lemma smoothEnergyPower_constant_stress (hc : A.toVertexAlgebra.C2Cofinite) (r : ℕ) (x : U.smoothEnergySpace) :
    U.smoothEnergyPower r x=
      ((((1:Module.End ℂ U.smoothEnergySpace)+U.smoothSmear hc A.conformal_mem
        (SmoothCircleFunction.constant 1).rapid_coefficients)^r) x:Completion V) := by
  induction r generalizing x with
  | zero => simpa only [pow_zero,Module.End.one_apply] using U.smoothEnergyPower_zero x
  | succ r ih =>
    rw [pow_succ]
    change _=((((1:Module.End ℂ U.smoothEnergySpace)+U.smoothSmear hc A.conformal_mem
        (SmoothCircleFunction.constant 1).rapid_coefficients)^r)
      (x+U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.constant 1).rapid_coefficients x):Completion V)
    rw [← ih]
    apply U.inverseSobolev_injective (r+1)
    rw [U.inverseSobolev_smoothEnergyPower]
    rw [Nat.add_comm r 1,← U.inverseSobolev_mul]
    change _=U.inverseSobolev 1 (U.inverseSobolev r (U.smoothEnergyPower r _))
    rw [U.inverseSobolev_smoothEnergyPower]
    change _=U.inverseSobolev 1 ((x:Completion V)+
      (U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.constant 1).rapid_coefficients x:Completion V))
    rw [← U.smoothEnergyPower_one_constant_stress hc,U.inverseSobolev_smoothEnergyPower]
def stressPropagatorSmoothEquiv (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath) (t : ℝ) :
    U.smoothEnergySpace ≃ₗᵢ[ℂ] U.smoothEnergySpace where
  toLinearEquiv :=
    { toLinearMap := U.stressPropagatorSmooth hc f t
      invFun := fun x => ⟨star (U.stressPropagator hc f t) x,U.stressPropagator_star_smooth hc f t x.property⟩
      left_inv := fun x => Subtype.ext ((U.stressPropagatorEquiv hc f t).symm_apply_apply x)
      right_inv := fun x => Subtype.ext ((U.stressPropagatorEquiv hc f t).apply_symm_apply x) }
  norm_map' := fun x => (U.stressPropagatorEquiv hc f t).norm_map x
lemma smoothSmear_smul (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f) (c : ℂ) :
    U.smoothSmear hc ha (hf.smul c)=c • U.smoothSmear hc ha hf := by
  obtain ⟨C,hC,p,k,hb⟩ := (U.polynomialEnergyBounds hc a).physical A d
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (U.smoothSmear hc ha (hf.smul c) x:Completion V)=c • (U.smoothSmear hc ha hf x:Completion V)
  rw [U.smoothSmear_eq_normalized hc ha hb,U.smoothSmear_eq_normalized hc ha hb,
    U.normalizedField_smul hc hb]
  rfl
lemma smoothSmear_constant (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (c : ℂ) :
    U.smoothSmear hc ha (SmoothCircleFunction.constant c).rapid_coefficients=
      c • U.smoothSmear hc ha (SmoothCircleFunction.constant 1).rapid_coefficients := by
  have he : (SmoothCircleFunction.constant c).coefficient=
      fun n => c*(SmoothCircleFunction.constant 1).coefficient n := by
    funext n
    simp only [SmoothCircleFunction.coefficient_constant,mul_ite,mul_one,mul_zero]
  conv_lhs => rw [show U.smoothSmear hc ha (SmoothCircleFunction.constant c).rapid_coefficients=
    U.smoothSmear hc ha ((SmoothCircleFunction.constant 1).rapid_coefficients.smul c) from by congr 1]
  exact U.smoothSmear_smul hc ha _ c
lemma primary_density_smooth_covariance (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {k : ℕ} (ha : a ∈ A.grade (k+1)) (hpa : A.IsPrimary a) (hh : U.IsHermitian (k+1) a)
    (φ : PositiveCircleGeometry.SmoothLift) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : Function.Periodic g 1) (t : ℝ) (y : U.smoothEnergySpace) :
    (U.smoothSmear hc ha (φ.angularDensity g hg hp k t).rapid_coefficients
      (U.stressPropagatorSmooth hc φ.angularStressPath t y):Completion V)=
      U.stressPropagator hc φ.angularStressPath t
        (U.smoothSmear hc ha (φ.angularDensity g hg hp k 0).rapid_coefficients y:Completion V) := by
  let G := φ.angularDensity g hg hp k
  apply U.primary_transport_smooth_covariance hc ha φ.angularStressPath (G 0).rapid_coefficients
    (G t).rapid_coefficients t
  intro x y
  apply U.primary_transport_form_constant hc ha hpa hh φ.angularStressPath
    (fun s => (G s).rapid_coefficients) (fun s => (G.timeDerivative s).rapid_coefficients)
    (S := Set.univ) convex_univ (Set.mem_univ 0) ?_ ?_ ?_ (Set.mem_univ t) x y
  · intro s _
    exact SmoothCircleFunction.coefficient_real (φ.angularDensity_real g hg hp k s)
  · intro s _ r
    exact G.seminorm_derivative s r
  · intro s _ r
    have he := (φ.angularVelocity s).hasSum_primaryTransport (G s) (k+1) r
    rw [← φ.angularDensity_transport g hg hp k s] at he
    exact he
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.PositiveCircleGeometry.Field
variable (f : Field (2*Real.pi))
def smoothCircle : SmoothCircleFunction where
  toFun := fun x => (f x:ℂ)
  periodic := fun x => congrArg Complex.ofReal (f.periodic x)
  smooth := Complex.ofRealCLM.contDiff.comp f.smooth
@[simp] lemma smoothCircle_apply (x : ℝ) : f.smoothCircle x=(f x:ℂ) := rfl
lemma smoothCircle_real : f.smoothCircle.IsReal := fun _ => Complex.conj_ofReal _
lemma flattening_angular_zero :
    f.flattening.angularDensity f.unitParameter f.unitParameter_smooth f.unitParameter_periodic 1 0=f.smoothCircle := by
  apply SmoothCircleFunction.ext
  intro x
  exact congrArg Complex.ofReal (f.flattening_realDensity_zero x)
lemma flattening_angular_one :
    f.flattening.angularDensity f.unitParameter f.unitParameter_smooth f.unitParameter_periodic 1 1=
      SmoothCircleFunction.constant f.frequency := by
  apply SmoothCircleFunction.ext
  intro x
  exact congrArg Complex.ofReal (f.flattening_realDensity_one x)
lemma flattening_primary_zero (k : ℕ) :
    f.flattening.angularDensity (fun x => f.unitParameter x^k) (f.unitParameter_smooth.pow k)
      (fun x => congrArg (fun y : ℝ => y^k) (f.unitParameter_periodic x)) k 0=f.smoothCircle.power k := by
  apply SmoothCircleFunction.ext
  intro x
  change (f.flattening.density (fun x => f.unitParameter x^k) k 0 (x/(2*Real.pi)):ℂ)=(f x:ℂ)^k
  rw [SmoothLift.density_power]
  rw [show f.flattening.density f.unitParameter 1 0 (x/(2*Real.pi))=f x from f.flattening_realDensity_zero x]
  exact Complex.ofReal_pow _ _
lemma flattening_primary_one (k : ℕ) :
    f.flattening.angularDensity (fun x => f.unitParameter x^k) (f.unitParameter_smooth.pow k)
      (fun x => congrArg (fun y : ℝ => y^k) (f.unitParameter_periodic x)) k 1=
        SmoothCircleFunction.constant ((f.frequency:ℂ)^k) := by
  apply SmoothCircleFunction.ext
  intro x
  change (f.flattening.density (fun x => f.unitParameter x^k) k 1 (x/(2*Real.pi)):ℂ)=(f.frequency:ℂ)^k
  rw [SmoothLift.density_power,f.flattening_density_one]
  exact Complex.ofReal_pow _ _
end StronglyRationalVOA.PositiveCircleGeometry.Field
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma primary_positive_local_bound (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {k : ℕ} (ha : a ∈ A.grade (k+1)) (hpa : A.IsPrimary a) (hh : U.IsHermitian (k+1) a)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ v, ‖A.physicalMode a (k+1) 0 v‖ ≤ C*‖(A.energyShift^k) v‖)
    (f : PositiveCircleGeometry.Field (2*Real.pi)) {M : ℝ}
    (hM : |f.frequency-f.stressScalar A.centralCharge.re| ≤ M) (x : U.smoothEnergySpace) :
    ‖(U.smoothSmear hc ha (f.smoothCircle.power k).rapid_coefficients x:Completion V)‖ ≤
      C*(1+M)^k*∑ j ∈ Finset.range (k+1),
        ‖(((U.smoothSmear hc A.conformal_mem f.smoothCircle.rapid_coefficients)^j) x:Completion V)‖ := by
  let e := U.stressPropagatorSmoothEquiv hc f.flattening.angularStressPath 1
  let P := U.smoothSmear hc ha (f.smoothCircle.power k).rapid_coefficients
  let P0 := U.smoothSmear hc ha (SmoothCircleFunction.constant 1).rapid_coefficients
  let T := U.smoothSmear hc A.conformal_mem f.smoothCircle.rapid_coefficients
  let L := U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.constant 1).rapid_coefficients
  have hg (y : U.smoothEnergySpace) : ‖P0 y‖ ≤ C*‖(((1:Module.End ℂ U.smoothEnergySpace)+L)^k) y‖ := by
    have h := U.smooth_constant_bound hc ha hC hb y
    rwa [U.smoothEnergyPower_constant_stress hc] at h
  have hP (y : U.smoothEnergySpace) : e (P y)=(f.frequency:ℂ)^k • P0 (e y) := by
    apply Subtype.ext
    have h := U.primary_density_smooth_covariance hc ha hpa hh f.flattening
      (fun z => f.unitParameter z^k) (f.unitParameter_smooth.pow k)
      (fun z => congrArg (fun w : ℝ => w^k) (f.unitParameter_periodic z)) 1 y
    rw [f.flattening_primary_zero,f.flattening_primary_one,U.smoothSmear_constant] at h
    exact h.symm
  have hT (y : U.smoothEnergySpace) :
      e (T y)=(f.frequency:ℂ) • L (e y)+(f.stressScalar A.centralCharge.re:ℂ) • e y := by
    apply Subtype.ext
    have h := U.stress_density_smooth_covariance hc f.flattening f.unitParameter
      f.unitParameter_smooth f.unitParameter_periodic f.unitParameter_pos 1 y
    rw [f.flattening_angular_zero,f.flattening_angular_one,U.smoothSmear_constant] at h
    have hcR : A.centralCharge=(A.centralCharge.re:ℂ) := Complex.ext rfl (by simp [U.centralCharge_nonneg.1])
    rw [hcR,f.flatteningShift] at h
    change (f.frequency:ℂ) • (L (e y):Completion V)=
      (e (T y):Completion V)+ ((-(f.stressScalar A.centralCharge.re):ℝ):ℂ) • (e y:Completion V) at h
    change (e (T y):Completion V)=(f.frequency:ℂ) • (L (e y):Completion V)+
      (f.stressScalar A.centralCharge.re:ℂ) • (e y:Completion V)
    rw [Complex.ofReal_neg,neg_smul,← sub_eq_add_neg] at h
    exact (eq_sub_iff_add_eq.mp h).symm
  exact LocalCovariance.bound_of_unitary_covariance e P P0 T L k hC hM hg hP hT x
lemma primary_strictPositive_localEnergy (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hpa : A.IsPrimary a) (hh : U.IsHermitian d a) (hd : 2 ≤ d)
    (f : PositiveCircleGeometry.Field (2*Real.pi)) : U.PrimaryLocalEnergyEstimate hc ha f.smoothCircle := by
  obtain ⟨C,hC,hb⟩ := U.optimal_quasiPrimary_energyBound hc ha (hpa 1 (by norm_num)) hh hd
  have hb0 (v : V) : ‖A.physicalMode a d 0 v‖ ≤ C*‖(A.energyShift^(d-1)) v‖ := by
    simpa only [Int.cast_zero,abs_zero,add_zero,one_pow,mul_one] using hb 0 v
  have he : d-1+1=d := by omega
  refine ⟨C*(1+|f.frequency-f.stressScalar A.centralCharge.re|)^(d-1),by positivity,?_⟩
  intro x
  have h := U.primary_positive_local_bound hc (he.symm ▸ ha) hpa (he.symm ▸ hh) hC.le
    (by simpa only [he] using hb0) f (le_rfl : |f.frequency-f.stressScalar A.centralCharge.re| ≤ _) x
  simpa only [he] using h
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set MeasureTheory
open scoped ContDiff
namespace StronglyRationalVOA.RealCircleCalculus
lemma average_bounds {T K : ℝ} (hT : 0 < T) {h : ℝ → ℝ} (hh : Continuous h)
    (hb : ∀ x ∈ Icc 0 T, 0 ≤ h x ∧ h x ≤ K) :
    0 ≤ T⁻¹*(∫ x in 0..T,h x) ∧ T⁻¹*(∫ x in 0..T,h x) ≤ K := by
  have hnon : 0 ≤ ∫ x in 0..T,h x := intervalIntegral.integral_nonneg hT.le (fun x hx => (hb x hx).1)
  have hupper := intervalIntegral.integral_mono_on (μ := volume) hT.le (hh.intervalIntegrable 0 T)
    (continuous_const.intervalIntegrable 0 T) (fun x hx => (hb x hx).2)
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hupper
  refine ⟨mul_nonneg (inv_nonneg.mpr hT.le) hnon,?_⟩
  calc
    _ ≤ T⁻¹*(T*K) := mul_le_mul_of_nonneg_left hupper (inv_nonneg.mpr hT.le)
    _ = K := by field_simp
end StronglyRationalVOA.RealCircleCalculus
namespace StronglyRationalVOA.PositiveCircleGeometry.Field
variable {T : ℝ} (f : Field T)
lemma frequency_sub_stressScalar_bound (hT : 0 < T) {K D : ℝ} (hK : 0 < K)
    (hf : ∀ x ∈ Icc 0 T, f x ≤ K) (hd : ∀ x ∈ Icc 0 T, (deriv f x)^2/f x ≤ D) (c : ℝ) :
    |f.frequency-f.stressScalar c| ≤ K+|c|/24*(2*K+D) := by
  have ha := RealCircleCalculus.average_bounds hT f.smooth.continuous
    (fun x hx => ⟨(f.positive x).le,hf x hx⟩)
  have hb := RealCircleCalculus.average_bounds hT
    (((contDiff_infty_iff_deriv.mp f.smooth).2.continuous.pow 2).div f.smooth.continuous
      (fun x => ne_of_gt (f.positive x)))
    (fun x hx => ⟨div_nonneg (sq_nonneg _) (f.positive x).le,hd x hx⟩)
  change 0 ≤ T⁻¹*(∫ x in 0..T,(deriv f x)^2/f x) ∧
    T⁻¹*(∫ x in 0..T,(deriv f x)^2/f x) ≤ D at hb
  rcases ha with ⟨ha0,ha1⟩
  rcases hb with ⟨hb0,hb1⟩
  have hfreq := f.frequency_le hT hK hf
  have hfreq0 := (f.frequency_pos hT).le
  have hinner : |T⁻¹*(∫ x in 0..T,f x)-f.frequency-T⁻¹*(∫ x in 0..T,(deriv f x)^2/f x)| ≤ 2*K+D :=
    abs_le.mpr ⟨by linarith,by linarith⟩
  rw [stressScalar]
  calc
    _ ≤ |f.frequency|+|c/24*(T⁻¹*(∫ x in 0..T,f x)-f.frequency-T⁻¹*(∫ x in 0..T,(deriv f x)^2/f x))| :=
      abs_sub _ _
    _ ≤ K+|c|/24*(2*K+D) := by
      rw [abs_of_nonneg hfreq0,abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ)<24)]
      exact add_le_add hfreq (mul_le_mul_of_nonneg_left hinner (by positivity))
end StronglyRationalVOA.PositiveCircleGeometry.Field
namespace StronglyRationalVOA.PositiveCircleGeometry
lemma quadratic_uniform_anomaly {T : ℝ} {g : ℝ → ℝ} (hp : Function.Periodic g T)
    (hs : ContDiff ℝ ∞ g) (hT : 0 < T) {M N : ℝ}
    (hM : ∀ x ∈ Icc 0 T, ‖g x‖ ≤ M) (hN : ∀ x ∈ Icc 0 T, ‖deriv g x‖ ≤ N)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (c : ℝ) :
    |(quadraticField hp hs hε).frequency-(quadraticField hp hs hε).stressScalar c| ≤
      (M^2+1)+|c|/24*(2*(M^2+1)+4*N^2) := by
  apply Field.frequency_sub_stressScalar_bound _ hT (by positivity)
  · intro x hx
    have hh := hM x hx
    rw [Real.norm_eq_abs] at hh
    have hsq := (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hh)).mpr hh
    simp only [sq_abs] at hsq
    change g x^2+ε ≤ M^2+1
    linarith
  · intro x hx
    apply (quadratic_logDerivative_bound hp hs hε x).trans
    have hh := hN x hx
    rw [Real.norm_eq_abs] at hh
    have hsq := (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hh)).mpr hh
    simp only [sq_abs] at hsq
    linarith
end StronglyRationalVOA.PositiveCircleGeometry

open UniformSpace Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.LocalCovariance
lemma continuous_power_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T L : Module.End ℂ E) (n : ℕ) (x : E) :
    Continuous (fun t : ℝ => ((T+(t:ℂ) • L)^n) x) := by
  induction n generalizing x with
  | zero => simpa only [pow_zero,Module.End.one_apply] using (continuous_const (y := x) : Continuous (fun _ : ℝ => x))
  | succ n ih =>
    have he (t : ℝ) : ((T+(t:ℂ) • L)^(n+1)) x=
        ((T+(t:ℂ) • L)^n) (T x)+(t:ℂ) • ((T+(t:ℂ) • L)^n) (L x) := by
      rw [pow_succ]
      change ((T+(t:ℂ) • L)^n) (T x+(t:ℂ) • L x)=_
      rw [map_add,map_smul]
    simp_rw [he]
    exact (ih (T x)).add (Complex.continuous_ofReal.smul (ih (L x)))
end StronglyRationalVOA.LocalCovariance
namespace StronglyRationalVOA.SmoothCircleFunction
def ofRealPeriodic (g : ℝ → ℝ) (hp : Function.Periodic g (2*Real.pi)) (hs : ContDiff ℝ ∞ g) : SmoothCircleFunction where
  toFun := fun x => (g x:ℂ)
  periodic := fun x => congrArg Complex.ofReal (hp x)
  smooth := Complex.ofRealCLM.contDiff.comp hs
@[simp] lemma ofRealPeriodic_apply (g : ℝ → ℝ) (hp : Function.Periodic g (2*Real.pi)) (hs : ContDiff ℝ ∞ g) (x : ℝ) :
    ofRealPeriodic g hp hs x=(g x:ℂ) := rfl
lemma ofRealPeriodic_real (g : ℝ → ℝ) (hp : Function.Periodic g (2*Real.pi)) (hs : ContDiff ℝ ∞ g) :
    (ofRealPeriodic g hp hs).IsReal := fun _ => Complex.conj_ofReal _
def quadraticFamily (g : SmoothCircleFunction) : SmoothCircleFamily where
  toFun t := (g.power 2).add (constant (t:ℂ))
  smooth := (g.smooth.comp contDiff_snd).pow 2 |>.add (Complex.ofRealCLM.contDiff.comp contDiff_fst)
def powerFamily (f : SmoothCircleFamily) (k : ℕ) : SmoothCircleFamily where
  toFun t := (f t).power k
  smooth := f.smooth.pow k
@[simp] lemma quadraticFamily_zero (g : SmoothCircleFunction) : quadraticFamily g 0=g.power 2 := by
  apply ext
  intro x
  simp only [quadraticFamily,add_apply,power_apply,constant_apply,Complex.ofReal_zero,add_zero]
end StronglyRationalVOA.SmoothCircleFunction
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma smoothSmear_sub (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) :
    U.smoothSmear hc ha (hf.sub hg)=U.smoothSmear hc ha hf-U.smoothSmear hc ha hg := by
  obtain ⟨C,hC,p,k,hb⟩ := (U.polynomialEnergyBounds hc a).physical A d
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (U.smoothSmear hc ha (hf.sub hg) x:Completion V)=
    (U.smoothSmear hc ha hf x:Completion V)-(U.smoothSmear hc ha hg x:Completion V)
  rw [U.smoothSmear_eq_normalized hc ha hb,U.smoothSmear_eq_normalized hc ha hb,
    U.smoothSmear_eq_normalized hc ha hb,U.normalizedField_sub hc hb]
  rfl
lemma smoothSmear_add (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) :
    U.smoothSmear hc ha (hf.add hg)=U.smoothSmear hc ha hf+U.smoothSmear hc ha hg := by
  have h := U.smoothSmear_sub hc ha (hf.add hg) hg
  have he : (fun n => (f n+g n)-g n)=f := funext fun _ => add_sub_cancel_right _ _
  rw [show U.smoothSmear hc ha ((hf.add hg).sub hg)=U.smoothSmear hc ha hf from by congr 1] at h
  exact (eq_sub_iff_add_eq.mp h).symm
lemma smoothSmear_add_functions (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (f g : SmoothCircleFunction) :
    U.smoothSmear hc ha (f.add g).rapid_coefficients=
      U.smoothSmear hc ha f.rapid_coefficients+U.smoothSmear hc ha g.rapid_coefficients := by
  have he : (f.add g).coefficient=fun n => f.coefficient n+g.coefficient n := funext (f.coefficient_add g)
  rw [show U.smoothSmear hc ha (f.add g).rapid_coefficients=
    U.smoothSmear hc ha (f.rapid_coefficients.add g.rapid_coefficients) from by congr 1]
  exact U.smoothSmear_add hc ha _ _
lemma smoothSmear_family_continuous (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (f : SmoothCircleFamily) (x : U.smoothEnergySpace) :
    Continuous (fun t => (U.smoothSmear hc ha (f t).rapid_coefficients x:Completion V)) := by
  obtain ⟨C,hC,p,k,hb⟩ := (U.polynomialEnergyBounds hc a).physical A d
  simp_rw [U.smoothSmear_eq_normalized hc ha hb]
  exact (U.normalizedField_continuous hc hC.le hb (fun t => (f t).rapid_coefficients)
    (fun t => f.seminorm_continuous t p)).clm_apply continuous_const
lemma quadratic_stress_powers_continuous (hc : A.toVertexAlgebra.C2Cofinite)
    (g : SmoothCircleFunction) (j : ℕ) (x : U.smoothEnergySpace) :
    Continuous (fun t : ℝ => (((U.smoothSmear hc A.conformal_mem
      (g.quadraticFamily t).rapid_coefficients)^j) x:Completion V)) := by
  have he (t : ℝ) : U.smoothSmear hc A.conformal_mem (g.quadraticFamily t).rapid_coefficients=
      U.smoothSmear hc A.conformal_mem (g.power 2).rapid_coefficients+
      (t:ℂ) • U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.constant 1).rapid_coefficients := by
    change U.smoothSmear hc A.conformal_mem ((g.power 2).add (SmoothCircleFunction.constant (t:ℂ))).rapid_coefficients=_
    rw [U.smoothSmear_add_functions,U.smoothSmear_constant]
  simp_rw [he]
  exact U.smoothEnergySpace.subtypeL.continuous.comp
    (LocalCovariance.continuous_power_affine _ _ j x)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
namespace StronglyRationalVOA.PositiveCircleGeometry
lemma quadratic_smoothCircle {g : ℝ → ℝ} (hp : Function.Periodic g (2*Real.pi))
    (hs : ContDiff ℝ ∞ g) {ε : ℝ} (hε : 0 < ε) :
    (quadraticField hp hs hε).smoothCircle=(SmoothCircleFunction.ofRealPeriodic g hp hs).quadraticFamily ε := by
  apply SmoothCircleFunction.ext
  intro x
  change ((g x^2+ε:ℝ):ℂ)=(g x:ℂ)^2+(ε:ℂ)
  push_cast
  rfl
end StronglyRationalVOA.PositiveCircleGeometry

open UniformSpace Filter Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

lemma primary_square_localEnergy (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hpa : A.IsPrimary a) (hh : U.IsHermitian d a) (hd : 2 ≤ d)
    {g : ℝ → ℝ} (hp : Function.Periodic g (2*Real.pi)) (hs : ContDiff ℝ ∞ g) :
    U.PrimaryLocalEnergyEstimate hc ha ((SmoothCircleFunction.ofRealPeriodic g hp hs).power 2) := by
  obtain ⟨C,hC,hb⟩ := U.optimal_quasiPrimary_energyBound hc ha (hpa 1 (by norm_num)) hh hd
  have hb0 (v : V) : ‖A.physicalMode a d 0 v‖ ≤ C*‖(A.energyShift^(d-1)) v‖ := by
    simpa only [Int.cast_zero,abs_zero,add_zero,one_pow,mul_one] using hb 0 v
  have he : d-1+1=d := by omega
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc 0 (2*Real.pi))).exists_bound_of_continuousOn hs.continuous.continuousOn
  obtain ⟨N,hN⟩ := (isCompact_Icc : IsCompact (Icc 0 (2*Real.pi))).exists_bound_of_continuousOn
    (contDiff_infty_iff_deriv.mp hs).2.continuous.continuousOn
  let K := (M^2+1)+|A.centralCharge.re|/24*(2*(M^2+1)+4*N^2)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let F := SmoothCircleFunction.ofRealPeriodic g hp hs
  let B := C*(1+K)^(d-1)
  refine ⟨B,by dsimp only [B]; positivity,?_⟩
  intro x
  let P : ℝ → ℝ := fun t => ‖(U.smoothSmear hc ha
    (SmoothCircleFunction.powerFamily F.quadraticFamily (d-1) t).rapid_coefficients x:Completion V)‖
  let R : ℝ → ℝ := fun t => B*∑ j ∈ Finset.range d,
    ‖(((U.smoothSmear hc A.conformal_mem (F.quadraticFamily t).rapid_coefficients)^j) x:Completion V)‖
  have hP : Continuous P := (U.smoothSmear_family_continuous hc ha
    (SmoothCircleFunction.powerFamily F.quadraticFamily (d-1)) x).norm
  have hR : Continuous R := continuous_const.mul (continuous_finsetSum _
    (fun j _ => (U.quadratic_stress_powers_continuous hc F j x).norm))
  let ε : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hε1 (n : ℕ) : ε n ≤ 1 := by
    dsimp only [ε]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hbound (n : ℕ) : P (ε n) ≤ R (ε n) := by
    have hgeom := PositiveCircleGeometry.quadratic_uniform_anomaly hp hs SmoothCircleFunction.period_pos
      hM hN (hε n) (hε1 n) A.centralCharge.re
    have h := U.primary_positive_local_bound hc (he.symm ▸ ha) hpa (he.symm ▸ hh) hC.le
      (by simpa only [he] using hb0) (PositiveCircleGeometry.quadraticField hp hs (hε n)) hgeom x
    rw [PositiveCircleGeometry.quadratic_smoothCircle] at h
    simpa only [P,R,B,K,SmoothCircleFunction.powerFamily,he] using h
  have hlim := le_of_tendsto_of_tendsto (hP.continuousAt.tendsto.comp hεlim)
    (hR.continuousAt.tendsto.comp hεlim) (Eventually.of_forall hbound)
  simpa only [P,R,SmoothCircleFunction.powerFamily,SmoothCircleFunction.quadraticFamily_zero] using hlim
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
open scoped ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

lemma primary_squarePower_selfAdjoint (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a)
    (hh : U.IsHermitian d a) (hd : 2 ≤ d)
    {g : ℝ → ℝ} (hper : Function.Periodic g (2*Real.pi)) (hs : ContDiff ℝ ∞ g) :
    IsSelfAdjoint (U.closedSmoothField hc a d
      (((SmoothCircleFunction.ofRealPeriodic g hper hs).power 2).power (d-1))) :=
  U.primary_power_selfAdjoint_of_localEstimate hc ha hp hh (by omega)
    (SmoothCircleFunction.power_real (SmoothCircleFunction.ofRealPeriodic_real g hper hs) 2)
    (U.primary_square_localEnergy hc ha hp hh hd hper hs)

 

lemma primary_squarePower_graph_locality (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hp : A.IsPrimary a) (hqb : A.IsQuasiPrimary b)
    (hha : U.IsHermitian d a) (hhb : U.IsHermitian e b) (hd : 2 ≤ d)
    {f : ℝ → ℝ} (hper : Function.Periodic f (2*Real.pi)) (hs : ContDiff ℝ ∞ f)
    {g : SmoothCircleFunction} (hg : g.IsReal)
    (hfg : Disjoint (tsupport (SmoothCircleFunction.ofRealPeriodic f hper hs)) (tsupport g))
    (i j k l : Bool) :
    ClosedGraphData.entry (U.closedSmoothField hc a d
        (((SmoothCircleFunction.ofRealPeriodic f hper hs).power 2).power (d-1)))
        (U.closedSmoothField_isClosed hc ha _) i j *
      ClosedGraphData.entry (U.closedSmoothField hc b e g)
        (U.closedSmoothField_isClosed hc hb _) k l =
    ClosedGraphData.entry (U.closedSmoothField hc b e g)
        (U.closedSmoothField_isClosed hc hb _) k l *
      ClosedGraphData.entry (U.closedSmoothField hc a d
        (((SmoothCircleFunction.ofRealPeriodic f hper hs).power 2).power (d-1)))
        (U.closedSmoothField_isClosed hc ha _) i j :=
  U.primary_power_graph_locality_of_localEstimate hc ha hb hp hqb hha hhb hd
    (SmoothCircleFunction.power_real (SmoothCircleFunction.ofRealPeriodic_real f hper hs) 2) hg
    (hfg.mono_left (SmoothCircleFunction.power_tsupport_subset _ (by norm_num)))
    (U.primary_square_localEnergy hc ha hp hha hd hper hs) i j k l
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction
lemma real_reconstruct (f : SmoothCircleFunction) (hf : f.IsReal) :
    ofRealPeriodic (fun t => (f t).re)
      (fun t => congrArg Complex.re (f.periodic t)) (Complex.reCLM.contDiff.comp f.smooth) = f := by
  ext t
  apply Complex.ext
  · rfl
  · have h := congrArg Complex.im (hf t)
    change 0 = (f t).im
    simp only [Complex.star_def,Complex.conj_im] at h
    linarith
lemma power_tsupport_eq (f : SmoothCircleFunction) {k : ℕ} (hk : 0 < k) :
    tsupport (f.power k) = tsupport f := by
  unfold tsupport
  congr 1
  ext t
  simp only [Function.mem_support,power_apply,ne_eq,pow_eq_zero_iff hk.ne']
lemma tsupport_lift_subset (f : SmoothCircleFunction) :
    tsupport f ⊆ (fun t : ℝ => (t : AddCircle (2*Real.pi))) ⁻¹' tsupport f.onCircle := by
  apply closure_minimal
  · intro t ht
    exact subset_closure ht
  · exact isClosed_closure.preimage (continuous_quotient_mk')
lemma disjoint_lift {f g : SmoothCircleFunction}
    (h : Disjoint (tsupport f.onCircle) (tsupport g.onCircle)) :
    Disjoint (tsupport f) (tsupport g) :=
  (h.preimage _).mono f.tsupport_lift_subset g.tsupport_lift_subset
end StronglyRationalVOA.SmoothCircleFunction
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma primary_realSquare_localEnergy (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a)
    (hh : U.IsHermitian d a) (hd : 2 ≤ d) {f : SmoothCircleFunction} (hf : f.IsReal) :
    U.PrimaryLocalEnergyEstimate hc ha (f.power 2) := by
  have h := U.primary_square_localEnergy hc ha hp hh hd (g := fun t => (f t).re)
    (fun t => congrArg Complex.re (f.periodic t)) (Complex.reCLM.contDiff.comp f.smooth)
  rwa [SmoothCircleFunction.real_reconstruct f hf] at h
 

structure PrimaryTestField where
  state : V
  weight : ℕ
  homogeneous : state ∈ A.grade weight
  quasiPrimary : A.IsQuasiPrimary state
  hermitian : U.IsHermitian weight state
  test : SmoothCircleFunction
  real : test.IsReal
  kind : weight = 1 ∨ (weight = 2 ∧ state = A.conformalVector) ∨
    (A.IsPrimary state ∧ 2 ≤ weight ∧ ∃ base : SmoothCircleFunction,
      base.IsReal ∧ test = (base.power 2).power (weight-1))
namespace PrimaryTestField
variable {U}
def field (F : U.PrimaryTestField) (hc : A.toVertexAlgebra.C2Cofinite) :=
  U.closedSmoothField hc F.state F.weight F.test
lemma closed (F : U.PrimaryTestField) (hc : A.toVertexAlgebra.C2Cofinite) :
    (F.field hc).IsClosed := U.closedSmoothField_isClosed hc F.homogeneous F.test
lemma selfAdjoint (F : U.PrimaryTestField) (hc : A.toVertexAlgebra.C2Cofinite) :
    IsSelfAdjoint (F.field hc) := by
  rcases F.kind with h | h | ⟨hp,hd,b,hb,he⟩
  · obtain ⟨C,hC,hbound⟩ := U.current_linear_energyBound hc (h ▸ F.homogeneous)
      F.quasiPrimary (h ▸ F.hermitian)
    have HB : ∀ n v, ‖A.physicalMode F.state F.weight n v‖ ≤ C*(1+|(n:ℝ)|)^1*‖A.energyShift v‖ := by
      simpa only [h,pow_one] using hbound
    exact U.smearedCore_essentialSelfAdjoint F.homogeneous F.quasiPrimary F.hermitian
      (U.polynomialEnergyBounds hc F.state) HB F.test.rapid_coefficients
      (SmoothCircleFunction.coefficient_real F.real)
  · rcases h with ⟨hw,ha⟩
    change IsSelfAdjoint (U.closedSmoothField hc F.state F.weight F.test)
    rw [hw,ha]
    exact U.stress_selfAdjoint hc F.real
  · change IsSelfAdjoint (U.closedSmoothField hc F.state F.weight F.test)
    rw [he]
    exact U.primary_power_selfAdjoint_of_localEstimate hc F.homogeneous hp F.hermitian (by omega)
      (SmoothCircleFunction.power_real hb 2) (U.primary_realSquare_localEnergy hc F.homogeneous hp F.hermitian hd hb)
end PrimaryTestField
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
