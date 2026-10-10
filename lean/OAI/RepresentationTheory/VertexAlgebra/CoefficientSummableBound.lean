import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.StressPropagatorDerivative

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
namespace StronglyRationalVOA

namespace SmoothCircleFunction

lemma coefficient_summable_bound (f : SmoothCircleFunction) (r : ℕ) {M : ℝ}
    (hM : 0 ≤ M) (h0 : ∀ x ∈ Icc 0 (2*Real.pi), ‖f x‖ ≤ M)
    (hk : ∀ x ∈ Icc 0 (2*Real.pi), ‖iteratedDeriv (r+2) f x‖ ≤ M) (n : ℤ) :
    ‖f.coefficient n‖*(1+|(n:ℝ)|)^r ≤ (2^(r+2)*M)*((1+|(n:ℝ)|)^2)⁻¹ := by
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1+|(n:ℝ)|) _)).mpr
  convert f.coefficient_weighted_bound (r+2) hM h0 hk n using 1
  first | rfl | (rw [pow_add]; ring)
end SmoothCircleFunction

lemma coefficientSeminorm_tendsto_zero {ι : Type*} {l : Filter ι} {f : ι → ℤ → ℂ} (r : ℕ)
    {C : ℝ} (hp : ∀ n, Tendsto (fun i => f i n) l (𝓝 0))
    (hb : ∀ᶠ i in l, ∀ n, ‖f i n‖*(1+|(n:ℝ)|)^r ≤ C*((1+|(n:ℝ)|)^2)⁻¹) :
    Tendsto (fun i => coefficientSeminorm (f i) r) l (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (summable_circle_decay.mul_left C)
    (f := fun i n => ‖f i n‖*(1+|(n:ℝ)|)^r) (g := fun _ : ℤ => (0:ℝ)) (fun n => by simpa using (hp n).norm.mul_const ((1+|(n:ℝ)|)^r))
    (hb.mono (fun i hi n => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact hi n))
  simpa only [tsum_zero,coefficientSeminorm] using h

 
structure SmoothCircleFamily where
  toFun : ℝ → SmoothCircleFunction
  smooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ => toFun p.1 p.2)
namespace SmoothCircleFamily
instance : CoeFun SmoothCircleFamily (fun _ => ℝ → SmoothCircleFunction) := ⟨SmoothCircleFamily.toFun⟩
variable (f : SmoothCircleFamily)
lemma time_smooth (x : ℝ) : ContDiff ℝ ∞ (fun t => f t x) :=
  f.smooth.comp (contDiff_id.prodMk contDiff_const)
lemma space_iterated_smooth (k : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv k (f p.1) p.2) :=
  joint_iterated_space_deriv_smooth f.smooth k
lemma time_derivative_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (fun t => f t p.2) p.1) := by
  have h := joint_space_deriv_smooth (f.smooth.comp (contDiff_snd.prodMk contDiff_fst))
  exact h.comp (contDiff_snd.prodMk contDiff_fst)

def timeDerivative : SmoothCircleFamily where
  toFun t := {
    toFun := fun x => deriv (fun s => f s x) t
    periodic := fun x => by
      have he : (fun s => f s (x+2*Real.pi))=(fun s => f s x) := funext fun s => (f s).periodic x
      exact congrArg (fun g : ℝ → ℂ => deriv g t) he
    smooth := f.time_derivative_smooth.comp (contDiff_const.prodMk contDiff_id) }
  smooth := f.time_derivative_smooth

lemma coefficient_derivative (t : ℝ) (n : ℤ) :
    HasDerivAt (fun s => (f s).coefficient n) ((f.timeDerivative t).coefficient n) t := by
  let K (x : ℝ) : ℂ := fourier (-n) (x : AddCircle (2*Real.pi))
  have hK : Continuous K := by unfold K; fun_prop
  let F (s x : ℝ) := K x*f s x
  let G (s x : ℝ) := K x*f.timeDerivative s x
  have hF (s : ℝ) : Continuous (F s) := hK.mul (f s).smooth.continuous
  have hG : Continuous (Function.uncurry G) :=
    (hK.comp continuous_snd).mul f.timeDerivative.smooth.continuous
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    hG.continuousOn (s := Icc (t-1) (t+1) ×ˢ Icc 0 (2*Real.pi))
  have hd := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := G) (μ := volume) (a := 0) (b := 2*Real.pi)
    (s := Icc (t-1) (t+1)) (bound := fun _ => M)
    (Icc_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall (fun s => (hF s).aestronglyMeasurable))
    ((hF t).intervalIntegrable _ _)
    ((hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun x hx s hs => hM (s,x) ⟨hs, by
      rw [uIoc_of_le SmoothCircleFunction.period_pos.le] at hx
      exact ⟨hx.1.le,hx.2⟩⟩))
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall (fun x _ s _ => by
      exact ((f.time_smooth x).differentiable (by simp) s).hasDerivAt.const_mul (K x)))
  have he (s : ℝ) : (f s).coefficient n = (1/(2*Real.pi):ℝ) • ∫ x in 0..2*Real.pi, F s x := by
    rw [SmoothCircleFunction.coefficient,fourierCoeffOn_eq_integral]
    simp only [sub_zero,smul_eq_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro x _
    simp only [F,K,fourier_coe_apply,sub_zero]
  have he' : (f.timeDerivative t).coefficient n = (1/(2*Real.pi):ℝ) • ∫ x in 0..2*Real.pi, G t x := by
    rw [SmoothCircleFunction.coefficient,fourierCoeffOn_eq_integral]
    simp only [sub_zero,smul_eq_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro x _
    simp only [G,K,fourier_coe_apply,sub_zero]
  simp_rw [he,he']
  exact hd.2.const_smul ((1/(2*Real.pi):ℝ))
end SmoothCircleFamily
end StronglyRationalVOA
namespace StronglyRationalVOA.SmoothCircleFamily
lemma coefficient_bound_compact (f : SmoothCircleFamily) (a b : ℝ) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ n : ℤ,
      ‖(f t).coefficient n‖*(1+|(n:ℝ)|)^r ≤ C*((1+|(n:ℝ)|)^2)⁻¹ := by
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    f.smooth.continuous.continuousOn (s := Icc a b ×ˢ Icc 0 (2*Real.pi))
  obtain ⟨N,hN⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (f.space_iterated_smooth (r+2)).continuous.continuousOn (s := Icc a b ×ˢ Icc 0 (2*Real.pi))
  let B := max 0 (max M N)
  have hB : 0 ≤ B := le_max_left _ _
  refine ⟨2^(r+2)*B,by positivity,fun t ht n => (f t).coefficient_summable_bound r hB ?_ ?_ n⟩
  · intro x hx
    exact (hM (t,x) ⟨ht,hx⟩).trans ((le_max_left M N).trans (le_max_right 0 _))
  · intro x hx
    exact (hN (t,x) ⟨ht,hx⟩).trans ((le_max_right M N).trans (le_max_right 0 _))

lemma seminorm_continuous (f : SmoothCircleFamily) (t : ℝ) (r : ℕ) :
    Tendsto (fun s => coefficientSeminorm (fun n => (f s).coefficient n-(f t).coefficient n) r)
      (𝓝 t) (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := f.coefficient_bound_compact (t-1) (t+1) r
  have ht : t ∈ Icc (t-1) (t+1) := ⟨by linarith,by linarith⟩
  apply coefficientSeminorm_tendsto_zero r (C := 2*C)
  · intro n
    simpa only [sub_self] using ((f.coefficient_derivative t n).continuousAt.tendsto.sub_const ((f t).coefficient n))
  · filter_upwards [Icc_mem_nhds (show t-1<t by linarith) (show t<t+1 by linarith)] with s hs
    intro n
    calc
      _ ≤ (‖(f s).coefficient n‖+‖(f t).coefficient n‖)*(1+|(n:ℝ)|)^r := by gcongr; exact norm_sub_le _ _
      _ = ‖(f s).coefficient n‖*(1+|(n:ℝ)|)^r+‖(f t).coefficient n‖*(1+|(n:ℝ)|)^r := by ring
      _ ≤ C*((1+|(n:ℝ)|)^2)⁻¹+C*((1+|(n:ℝ)|)^2)⁻¹ := add_le_add (hb s hs n) (hb t ht n)
      _ = _ := by ring
end StronglyRationalVOA.SmoothCircleFamily
namespace StronglyRationalVOA.SmoothCircleFamily
lemma seminorm_derivative (f : SmoothCircleFamily) (t : ℝ) (r : ℕ) :
    Tendsto (fun s => coefficientSeminorm
      (fun n => (((s-t)⁻¹:ℝ):ℂ)*((f s).coefficient n-(f t).coefficient n)-
        (f.timeDerivative t).coefficient n) r) (𝓝[≠] t) (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := f.timeDerivative.coefficient_bound_compact (t-1) (t+1) r
  have ht : t ∈ Icc (t-1) (t+1) := ⟨by linarith,by linarith⟩
  apply coefficientSeminorm_tendsto_zero r (C := 2*C)
  · intro n
    have h := (hasDerivAt_iff_tendsto_slope.mp (f.coefficient_derivative t n)).sub_const
      ((f.timeDerivative t).coefficient n)
    simpa only [slope,vsub_eq_sub,sub_self,Complex.real_smul] using h
  · have hnh : Icc (t-1) (t+1) ∈ 𝓝[≠] t := nhdsWithin_le_nhds (Icc_mem_nhds (by linarith) (by linarith))
    filter_upwards [hnh,self_mem_nhdsWithin] with s hs hst
    have hne : s-t ≠ 0 := sub_ne_zero.mpr hst
    intro n
    let W : ℝ := (1+|(n:ℝ)|)^r
    have hW : 0 < W := pow_pos (by positivity) _
    have hder (u : ℝ) (_hu : u ∈ Icc (t-1) (t+1)) :
        HasDerivWithinAt (fun q => (W:ℂ)*(f q).coefficient n)
          ((W:ℂ)*(f.timeDerivative u).coefficient n) (Icc (t-1) (t+1)) u :=
      ((f.coefficient_derivative u n).const_mul (W:ℂ)).hasDerivWithinAt
    have hbd (u : ℝ) (hu : u ∈ Icc (t-1) (t+1)) :
        ‖(W:ℂ)*(f.timeDerivative u).coefficient n‖ ≤ C*((1+|(n:ℝ)|)^2)⁻¹ := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hW,mul_comm]
      exact hb u hu n
    have hd := (convex_Icc (t-1) (t+1)).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd ht hs
    rw [← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hW] at hd
    have hsl : ‖(((s-t)⁻¹:ℝ):ℂ)*((f s).coefficient n-(f t).coefficient n)‖*W ≤
        C*((1+|(n:ℝ)|)^2)⁻¹ := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_inv]
      calc
        _ = (W*‖(f s).coefficient n-(f t).coefficient n‖)*|s-t|⁻¹ := by ring
        _ ≤ (C*((1+|(n:ℝ)|)^2)⁻¹*‖s-t‖)*|s-t|⁻¹ := mul_le_mul_of_nonneg_right hd (inv_nonneg.mpr (abs_nonneg _))
        _ = _ := by rw [Real.norm_eq_abs,mul_assoc,mul_inv_cancel₀ (abs_ne_zero.mpr hne),mul_one]
    calc
      _ ≤ (‖(((s-t)⁻¹:ℝ):ℂ)*((f s).coefficient n-(f t).coefficient n)‖+
        ‖(f.timeDerivative t).coefficient n‖)*W := by gcongr; exact norm_sub_le _ _
      _ = _ := add_mul _ _ _
      _ ≤ C*((1+|(n:ℝ)|)^2)⁻¹+C*((1+|(n:ℝ)|)^2)⁻¹ := add_le_add hsl (hb t ht n)
      _ = _ := by ring
end StronglyRationalVOA.SmoothCircleFamily
namespace StronglyRationalVOA.SmoothCircleFamily
lemma seminorm_bound_stationary (f : SmoothCircleFamily) (a b : ℝ)
    (hz : ∀ t ∉ Icc a b, ∀ x, f t x=0) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, coefficientSeminorm (f t).coefficient r ≤ C := by
  obtain ⟨C,hC,hb⟩ := f.coefficient_bound_compact a b r
  let D := ∑' n : ℤ, C*((1+|(n:ℝ)|)^2)⁻¹
  have hD : 0 ≤ D := tsum_nonneg (fun n => by positivity)
  refine ⟨D,hD,fun t => ?_⟩
  by_cases ht : t ∈ Icc a b
  · exact Summable.tsum_le_tsum (hb t ht) ((f t).rapid_coefficients r) (summable_circle_decay.mul_left C)
  · have he (n : ℤ) : (f t).coefficient n=0 := by
      rw [SmoothCircleFunction.coefficient,fourierCoeffOn_eq_integral]
      simp only [hz t ht,smul_zero,intervalIntegral.integral_zero]
    simpa only [coefficientSeminorm,he,norm_zero,zero_mul,tsum_zero] using hD

def toStressPath (f : SmoothCircleFamily) (hr : ∀ t, (f t).IsReal) (a b : ℝ)
    (hz : ∀ t ∉ Icc a b, ∀ x, f t x=0) : CFTTypeVOA.UnitaryStructure.StressPath where
  coefficients t := (f t).coefficient
  rapid t := (f t).rapid_coefficients
  real t := SmoothCircleFunction.coefficient_real (hr t)
  continuous t := f.seminorm_continuous t 2
  bound r := (f.seminorm_bound_stationary a b hz r).choose
  bound_nonneg r := (f.seminorm_bound_stationary a b hz r).choose_spec.1
  seminorm_bound t r := (f.seminorm_bound_stationary a b hz r).choose_spec.2 t
end StronglyRationalVOA.SmoothCircleFamily

open Filter Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction
@[ext] lemma ext {f g : SmoothCircleFunction} (h : ∀ x, f x=g x) : f=g := by
  cases f
  cases g
  congr
  exact funext h
end StronglyRationalVOA.SmoothCircleFunction
namespace StronglyRationalVOA.PositiveCircleGeometry.SmoothLift
variable (φ : SmoothLift)
private lemma angular_shift (x : ℝ) : (x+2*Real.pi)/(2*Real.pi)=x/(2*Real.pi)+1 := by
  field_simp [Real.pi_ne_zero]

def angularVelocity : SmoothCircleFamily where
  toFun t := {
    toFun := fun x => (2*Real.pi*φ.velocity t (x/(2*Real.pi)) : ℝ)
    periodic := fun x => by
      dsimp only
      rw [angular_shift,φ.velocity_periodic]
    smooth := Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul ((φ.velocity_smooth.comp (contDiff_const.prodMk (contDiff_id.div_const _))))) }
  smooth := Complex.ofRealCLM.contDiff.comp
    (contDiff_const.mul (φ.velocity_smooth.comp (contDiff_fst.prodMk (contDiff_snd.div_const _))))
lemma angularVelocity_real (t : ℝ) : (φ.angularVelocity t).IsReal := fun x => by
  change star ((2*Real.pi*φ.velocity t (x/(2*Real.pi)):ℝ):ℂ)=_
  exact Complex.conj_ofReal _
lemma angularVelocity_stationary (t : ℝ) (ht : t ∉ Icc 0 1) (x : ℝ) : φ.angularVelocity t x=0 := by
  change ((2*Real.pi*φ.velocity t (x/(2*Real.pi)):ℝ):ℂ)=0
  simp only [φ.velocity_stationary ht,Pi.zero_apply,mul_zero,Complex.ofReal_zero]
def angularStressPath : CFTTypeVOA.UnitaryStructure.StressPath :=
  φ.angularVelocity.toStressPath φ.angularVelocity_real 0 1 φ.angularVelocity_stationary

def angularDensity (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g 1) (k : ℕ) :
    SmoothCircleFamily where
  toFun t := {
    toFun := fun x => (φ.density g k t (x/(2*Real.pi)) : ℝ)
    periodic := fun x => by dsimp only; rw [angular_shift,φ.density_periodic hp]
    smooth := Complex.ofRealCLM.contDiff.comp ((φ.density_smooth hg k).comp
      (contDiff_const.prodMk (contDiff_id.div_const _))) }
  smooth := Complex.ofRealCLM.contDiff.comp ((φ.density_smooth hg k).comp
    (contDiff_fst.prodMk (contDiff_snd.div_const _)))
lemma angularDensity_real (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g 1)
    (k : ℕ) (t : ℝ) : (φ.angularDensity g hg hp k t).IsReal := fun _ => Complex.conj_ofReal _
lemma angularVelocity_space_derivative (t x : ℝ) :
    HasDerivAt (φ.angularVelocity t) (deriv (φ.velocity t) (x/(2*Real.pi)):ℝ) x := by
  have hv := (((φ.velocity_smooth.comp ((contDiff_const (c := t)).prodMk contDiff_id)).differentiable
    (by simp) (x/(2*Real.pi))).hasDerivAt).comp x ((hasDerivAt_id x).div_const (2*Real.pi))
  have hd := (hv.const_mul (2*Real.pi)).ofReal_comp
  convert hd using 1 <;> first | rfl | (congr 1; dsimp only [Function.comp_def,id_eq]; field_simp [Real.pi_ne_zero])
lemma angularDensity_space_derivative (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g 1)
    (k : ℕ) (t x : ℝ) :
    HasDerivAt (φ.angularDensity g hg hp k t)
      ((deriv (φ.density g k t) (x/(2*Real.pi))/(2*Real.pi):ℝ):ℂ) x := by
  have hv := (((φ.density_smooth hg k).comp ((contDiff_const (c := t)).prodMk contDiff_id)).differentiable
    (by simp) (x/(2*Real.pi))).hasDerivAt.comp x ((hasDerivAt_id x).div_const (2*Real.pi))
  convert hv.ofReal_comp using 1 <;> first | rfl | (congr 1; dsimp only [Function.comp_def,id_eq]; ring)
lemma angularDensity_transport (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g 1)
    (k : ℕ) (t : ℝ) :
    (φ.angularDensity g hg hp k).timeDerivative t =
      (φ.angularVelocity t).primaryTransport (φ.angularDensity g hg hp k t) (k+1) := by
  apply SmoothCircleFunction.ext
  intro x
  change deriv (fun s => ((φ.density g k s (x/(2*Real.pi)):ℝ):ℂ)) t=_
  rw [(φ.density_time_derivative hg k t (x/(2*Real.pi))).ofReal_comp.deriv,
    SmoothCircleFunction.primaryTransport_apply,(φ.angularVelocity_space_derivative t x).deriv,
    (φ.angularDensity_space_derivative g hg hp k t x).deriv]
  change _ = ((↑(k+1):ℂ)-1)*(deriv (φ.velocity t) (x/(2*Real.pi)):ℝ)*
      (φ.density g k t (x/(2*Real.pi)):ℝ)-
      (2*Real.pi*φ.velocity t (x/(2*Real.pi)):ℝ)*
      (deriv (φ.density g k t) (x/(2*Real.pi))/(2*Real.pi):ℝ)
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring
end StronglyRationalVOA.PositiveCircleGeometry.SmoothLift
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

lemma primary_density_closed_covariance (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {k : ℕ} (ha : a ∈ A.grade (k+1)) (hpa : A.IsPrimary a) (hh : U.IsHermitian (k+1) a)
    (φ : PositiveCircleGeometry.SmoothLift) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : Function.Periodic g 1) (t : ℝ) :
    OperatorTransport.transport (U.stressPropagatorEquiv hc φ.angularStressPath t)
      (U.closedSmoothField hc a (k+1) (φ.angularDensity g hg hp k t)) =
        U.closedSmoothField hc a (k+1) (φ.angularDensity g hg hp k 0) := by
  let G := φ.angularDensity g hg hp k
  have hf (s : ℝ) := (G s).rapid_coefficients
  have hf' (s : ℝ) := (G.timeDerivative s).rapid_coefficients
  apply U.stress_transport_closed_graph hc ha φ.angularStressPath (hf 0) (hf t) t
  apply U.primary_transport_smooth_covariance hc ha φ.angularStressPath (hf 0) (hf t) t
  intro x y
  apply U.primary_transport_form_constant hc ha hpa hh φ.angularStressPath hf hf'
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
namespace StronglyRationalVOA.SmoothCircleFunction
 
def cocycleDensity (f g : SmoothCircleFunction) : SmoothCircleFunction :=
  ((f.differentiated 3).add (f.differentiated 1)).mul g
lemma hasSum_cocycleDensity (f g : SmoothCircleFunction) :
    HasSum (fun m : ℤ => ((m:ℂ)^3-m)*f.coefficient m*g.coefficient (-m))
      (Complex.I*(f.cocycleDensity g).coefficient 0) := by
  have h := (((f.differentiated 3).coefficient_mul g 0).add
    ((f.differentiated 1).coefficient_mul g 0)).mul_left Complex.I
  rw [cocycleDensity]
  have he : ((f.differentiated 3).add (f.differentiated 1)).mul g =
      ((f.differentiated 3).mul g).add ((f.differentiated 1).mul g) := by
    apply ext; intro x; simp only [mul_apply,add_apply]; ring
  rw [he,coefficient_add]
  apply h.congr_fun
  intro m
  simp only [coefficient_differentiated,zero_sub,pow_one]
  ring_nf
  norm_num [Complex.I_sq]
end StronglyRationalVOA.SmoothCircleFunction
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma sobolevExtension_weakCommutator_central (r : ℕ) (M N Q : V →ₗ[ℂ] Completion V) {C D E : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖)
    (hN : ∀ v, ‖N v‖ ≤ D*‖(A.energyShift^r) v‖)
    (hQ : ∀ v, ‖Q v‖ ≤ E*‖(A.energyShift^r) v‖) (c w : ℂ)
    (hw : ∀ x y, inner ℂ (M x) (N y)-inner ℂ (N x) (M y)=c*inner ℂ (x:Completion V) (Q y)+w*inner ℂ x y)
    (x y : Completion V) :
    inner ℂ (U.sobolevExtension r M x) (U.sobolevExtension r N y)-
      inner ℂ (U.sobolevExtension r N x) (U.sobolevExtension r M y)=
      c*inner ℂ (U.inverseSobolev r x) (U.sobolevExtension r Q y)+
      w*inner ℂ (U.inverseSobolev r x) (U.inverseSobolev r y) := by
  have hd : DenseRange (fun v : V => (v:Completion V)) := Completion.denseRange_coe
  refine hd.induction_on₂ ?_ ?_ x y
  · exact isClosed_eq
      ((((U.sobolevExtension r M).continuous.comp continuous_fst).inner
        ((U.sobolevExtension r N).continuous.comp continuous_snd)).sub
        (((U.sobolevExtension r N).continuous.comp continuous_fst).inner
          ((U.sobolevExtension r M).continuous.comp continuous_snd)))
      ((continuous_const.mul (((U.inverseSobolev r).continuous.comp continuous_fst).inner
        ((U.sobolevExtension r Q).continuous.comp continuous_snd))).add
        (continuous_const.mul (((U.inverseSobolev r).continuous.comp continuous_fst).inner
          ((U.inverseSobolev r).continuous.comp continuous_snd))))
  · intro v w
    simpa only [U.sobolevExtension_coe r M hM,U.sobolevExtension_coe r N hN,
      U.sobolevExtension_coe r Q hQ,← U.inverseCoreEnergy_coe,Completion.inner_coe] using
        hw (U.inverseCoreEnergy r v) (U.inverseCoreEnergy r w)

lemma smoothSmear_weakCommutator_central_of_algebraic (hc : A.toVertexAlgebra.C2Cofinite)
    {a b c : V} {d e j : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hcj : c ∈ A.grade j)
    {f g h : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) (hh : RapidCoefficients h)
    (z w : ℂ)
    (hweak : ∀ x y : V,
      inner ℂ (A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf x)
        (A.smearedMap b e (U.polynomialEnergyBounds hc b) g hg y)-
      inner ℂ (A.smearedMap b e (U.polynomialEnergyBounds hc b) g hg x)
        (A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf y)=
      z*inner ℂ (x:Completion V) (A.smearedMap c j (U.polynomialEnergyBounds hc c) h hh y)+w*inner ℂ x y)
    (x y : U.smoothEnergySpace) :
    inner ℂ (U.smoothSmear hc ha hf x : Completion V) (U.smoothSmear hc hb hg y : Completion V)-
      inner ℂ (U.smoothSmear hc hb hg x : Completion V) (U.smoothSmear hc ha hf y : Completion V)=
      z*inner ℂ (x:Completion V) (U.smoothSmear hc hcj hh y : Completion V)+w*inner ℂ (x:Completion V) (y:Completion V) := by
  obtain ⟨C,hC,p,k,hM⟩ := (U.polynomialEnergyBounds hc a).physical A d
  obtain ⟨D,hD,q,l,hN⟩ := (U.polynomialEnergyBounds hc b).physical A e
  obtain ⟨E,hE,o,m,hQ⟩ := (U.polynomialEnergyBounds hc c).physical A j
  let M := A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf
  let N := A.smearedMap b e (U.polynomialEnergyBounds hc b) g hg
  let Q := A.smearedMap c j (U.polynomialEnergyBounds hc c) h hh
  have hm (v : V) : ‖M v‖ ≤ (coefficientSeminorm f p*C)*‖(A.energyShift^(k+l+m)) v‖ :=
    (A.smearedMap_bound _ hf hM v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : k ≤ k+l+m) v)
        (mul_nonneg (coefficientSeminorm_nonneg _ _) hC.le))
  have hn (v : V) : ‖N v‖ ≤ (coefficientSeminorm g q*D)*‖(A.energyShift^(k+l+m)) v‖ :=
    (A.smearedMap_bound _ hg hN v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : l ≤ k+l+m) v)
        (mul_nonneg (coefficientSeminorm_nonneg _ _) hD.le))
  have hq (v : V) : ‖Q v‖ ≤ (coefficientSeminorm h o*E)*‖(A.energyShift^(k+l+m)) v‖ :=
    (A.smearedMap_bound _ hh hQ v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : m ≤ k+l+m) v)
        (mul_nonneg (coefficientSeminorm_nonneg _ _) hE.le))
  rw [U.smoothSmear_eq_extension hc ha hf hm x (U.smoothEnergyPower_graph (k+l+m) x),
    U.smoothSmear_eq_extension hc hb hg hn y (U.smoothEnergyPower_graph (k+l+m) y),
    U.smoothSmear_eq_extension hc hb hg hn x (U.smoothEnergyPower_graph (k+l+m) x),
    U.smoothSmear_eq_extension hc ha hf hm y (U.smoothEnergyPower_graph (k+l+m) y),
    U.smoothSmear_eq_extension hc hcj hh hq y (U.smoothEnergyPower_graph (k+l+m) y),
    U.sobolevExtension_weakCommutator_central (k+l+m) M N Q hm hn hq z w hweak,
    U.inverseSobolev_smoothEnergyPower,U.inverseSobolev_smoothEnergyPower]

lemma stress_stress_weakCommutator (hc : A.toVertexAlgebra.C2Cofinite)
    (f g : SmoothCircleFunction) (hfr : f.IsReal) (hgr : g.IsReal) (x y : V) :
    inner ℂ (A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector) f.coefficient f.rapid_coefficients x)
      (A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector) g.coefficient g.rapid_coefficients y)-
    inner ℂ (A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector) g.coefficient g.rapid_coefficients x)
      (A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector) f.coefficient f.rapid_coefficients y)=
    -Complex.I*inner ℂ (x:Completion V)
      (A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector)
        (f.primaryTransport g 2).coefficient (f.primaryTransport g 2).rapid_coefficients y) +
      (A.centralCharge/12)*(Complex.I*(f.cocycleDensity g).coefficient 0)*inner ℂ x y := by
  have hν : U.IsHermitian 2 A.conformalVector := by simp [IsHermitian,U.pct_conformal]
  let M := A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector) f.coefficient f.rapid_coefficients
  let N := A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector) g.coefficient g.rapid_coefficients
  let Q := A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector)
    (f.primaryTransport g 2).coefficient (f.primaryTransport g 2).rapid_coefficients
  let c : ℂ := (A.centralCharge/12)*(Complex.I*(f.cocycleDensity g).coefficient 0)
  have hv (n : ℤ) : A.physicalMode A.conformalVector 2 n=A.virasoroMode n := by
    unfold physicalMode virasoroMode; congr 1; omega
  have Hhom (D E : ℕ) (x y : V) (hx : x ∈ A.grade D) (hy : y ∈ A.grade E) :
      inner ℂ (M x) (N y)-inner ℂ (N x) (M y) =
        -Complex.I*inner ℂ (x:Completion V) (Q y)+c*inner ℂ x y := by
    let r : ℤ := (E:ℤ)-D
    have H1 := U.hasSum_smeared_inner_homogeneous A.conformal_mem A.conformal_mem hx hy
      A.conformal_quasiPrimary hν (U.polynomialEnergyBounds hc A.conformalVector)
      (U.polynomialEnergyBounds hc A.conformalVector) f.rapid_coefficients g.rapid_coefficients
      (SmoothCircleFunction.coefficient_real hfr)
    have H2 := U.hasSum_smeared_inner_homogeneous A.conformal_mem A.conformal_mem hx hy
      A.conformal_quasiPrimary hν (U.polynomialEnergyBounds hc A.conformalVector)
      (U.polynomialEnergyBounds hc A.conformalVector) g.rapid_coefficients f.rapid_coefficients
      (SmoothCircleFunction.coefficient_real hgr)
    let R : ℤ ≃ ℤ :=
      { toFun := fun m => r-m
        invFun := fun m => r-m
        left_inv := fun m => by dsimp; omega
        right_inv := fun m => by dsimp; omega }
    have Hdiff := H1.sub (R.hasSum_iff.mpr H2)
    have Hz := (f.hasSum_primaryTransport g 2 r).mul_right (inner ℂ x (A.virasoroMode r y))
    have Hc : HasSum (fun m : ℤ => f.coefficient m*g.coefficient (r-m)*
        (if r=0 then (A.centralCharge/12)*((m:ℂ)^3-m) else 0)*inner ℂ x y)
        (c*inner ℂ x y) := by
      by_cases hr : r=0
      · simp only [hr,zero_sub,ite_eq_left]
        apply (((f.hasSum_cocycleDensity g).mul_left (A.centralCharge/12)).mul_right (inner ℂ x y)).congr_fun
        intro m; ring
      · have hin : inner ℂ x y=0 := U.grades_orthogonal (by intro he; apply hr; dsimp [r]; simp [he]) hx hy
        simp only [ite_eq_right hr,hin,mul_zero]
        exact hasSum_zero
    have He : HasSum (fun m : ℤ => f.coefficient m*g.coefficient (r-m)*inner ℂ x
        (A.virasoroMode m (A.virasoroMode (r-m) y)-
          A.virasoroMode (r-m) (A.virasoroMode m y)))
        (-Complex.I*inner ℂ (x:Completion V) (Q y)+c*inner ℂ x y) := by
      have hs := Hz.add Hc
      change HasSum _ (-Complex.I*inner ℂ (x:Completion V)
        (A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector)
          (f.primaryTransport g 2).coefficient (f.primaryTransport g 2).rapid_coefficients y)+_) 
      rw [U.inner_smearedMap_homogeneous A.conformal_mem hx hy,hv]
      change HasSum _ (-Complex.I*((f.primaryTransport g 2).coefficient r*inner ℂ x (A.virasoroMode r y))+c*inner ℂ x y)
      rw [← mul_assoc]
      apply hs.congr_fun
      intro m
      rw [A.virasoro_commutator,show m+(r-m)=r by omega,inner_add_right,inner_smul_right,inner_smul_right]
      push_cast
      norm_num
      split_ifs <;> ring
    apply Hdiff.unique
    convert He using 1
    ext m
    simp only [Function.comp_def,R,Equiv.coe_fn_mk]
    rw [show (E:ℤ)-D-(r-m)=m by dsimp [r]; omega]
    simp only [hv,inner_sub_right]
    ring
  change inner ℂ (M x) (N y)-inner ℂ (N x) (M y) =
    -Complex.I*inner ℂ (x:Completion V) (Q y)+c*inner ℂ x y
  apply A.homogeneous_induction (P := fun x => inner ℂ (M x) (N y)-inner ℂ (N x) (M y) =
    -Complex.I*inner ℂ (x:Completion V) (Q y)+c*inner ℂ x y)
  · simp only [map_zero,inner_zero_left,sub_self,Completion.coe_zero,mul_zero,add_zero]
  · intro D x hx
    apply A.homogeneous_induction (P := fun y => inner ℂ (M x) (N y)-inner ℂ (N x) (M y) =
      -Complex.I*inner ℂ (x:Completion V) (Q y)+c*inner ℂ x y)
    · simp
    · intro E y hy; exact Hhom D E x y hx hy
    · intro y z hy hz
      simp only [map_add,inner_add_right]
      linear_combination hy+hz
  · intro x z hx hz
    simp only [map_add,inner_add_left,Completion.coe_add]
    linear_combination hx+hz
lemma stress_stress_smoothCommutator (hc : A.toVertexAlgebra.C2Cofinite)
    (f g : SmoothCircleFunction) (hfr : f.IsReal) (hgr : g.IsReal) (x y : U.smoothEnergySpace) :
    inner ℂ (U.smoothSmear hc A.conformal_mem f.rapid_coefficients x : Completion V)
      (U.smoothSmear hc A.conformal_mem g.rapid_coefficients y : Completion V)-
    inner ℂ (U.smoothSmear hc A.conformal_mem g.rapid_coefficients x : Completion V)
      (U.smoothSmear hc A.conformal_mem f.rapid_coefficients y : Completion V)=
    -Complex.I*inner ℂ (x:Completion V)
      (U.smoothSmear hc A.conformal_mem (f.primaryTransport g 2).rapid_coefficients y : Completion V) +
      (A.centralCharge/12)*(Complex.I*(f.cocycleDensity g).coefficient 0)*inner ℂ (x:Completion V) (y:Completion V) := by
  exact U.smoothSmear_weakCommutator_central_of_algebraic hc A.conformal_mem A.conformal_mem A.conformal_mem
    f.rapid_coefficients g.rapid_coefficients (f.primaryTransport g 2).rapid_coefficients _ _
    (U.stress_stress_weakCommutator hc f g hfr hgr) x y

lemma stress_density_form_derivative (hc : A.toVertexAlgebra.C2Cofinite)
    (φ : PositiveCircleGeometry.SmoothLift) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : Function.Periodic g 1) (t : ℝ) (x y : U.smoothEnergySpace) :
    HasDerivAt (fun s => inner ℂ (U.stressPropagator hc φ.angularStressPath s x)
      (U.smoothSmear hc A.conformal_mem (φ.angularDensity g hg hp 1 s).rapid_coefficients
        (U.stressPropagatorSmooth hc φ.angularStressPath s y) : Completion V))
      ((A.centralCharge/12)*((φ.angularVelocity t).cocycleDensity (φ.angularDensity g hg hp 1 t)).coefficient 0*
        inner ℂ (x:Completion V) (y:Completion V)) t := by
  let f := φ.angularStressPath
  let G := φ.angularDensity g hg hp 1
  have hν : U.IsHermitian 2 A.conformalVector := by simp [IsHermitian,U.pct_conformal]
  obtain ⟨C,hC,p,k,hb⟩ := (U.polynomialEnergyBounds hc A.conformalVector).physical A 2
  have hd := U.smoothSmear_form_derivative hc A.conformal_mem A.conformal_quasiPrimary hν hC.le hb
    (fun s => (G s).rapid_coefficients) (G.timeDerivative t).rapid_coefficients t
    (SmoothCircleFunction.coefficient_real (φ.angularDensity_real g hg hp 1 t)) (G.seminorm_derivative t p)
    (fun s => U.stressPropagatorSmooth hc f s x) (fun s => U.stressPropagatorSmooth hc f s y)
    _ _ (U.stressPropagator_derivative hc f t x) (U.stressPropagator_derivative hc f t y)
    (U.stressPropagatorSmooth_continuous_power hc f k y).continuousAt
  have hw := U.stress_stress_smoothCommutator hc (φ.angularVelocity t) (G t)
    (φ.angularVelocity_real t) (φ.angularDensity_real g hg hp 1 t)
    (U.stressPropagatorSmooth hc f t x) (U.stressPropagatorSmooth hc f t y)
  have he : G.timeDerivative t=(φ.angularVelocity t).primaryTransport (G t) 2 :=
    φ.angularDensity_transport g hg hp 1 t
  rw [he,U.stressPropagatorDerivative_smoothSmear hc f t x,
    U.stressPropagatorDerivative_smoothSmear hc f t y,inner_smul_left,inner_smul_right,Complex.conj_I] at hd
  have hi := (U.stressPropagatorEquiv hc f t).inner_map_map (x:Completion V) (y:Completion V)
  change inner ℂ (U.stressPropagatorSmooth hc f t x : Completion V)
    (U.stressPropagatorSmooth hc f t y : Completion V)=inner ℂ (x:Completion V) (y:Completion V) at hi
  rw [hi] at hw
  convert hd using 1 <;> try rfl
  have hz := congrArg (fun z : ℂ => -Complex.I*z) hw
  simp only [mul_add,mul_sub,neg_mul_neg,← mul_assoc,Complex.I_mul_I,neg_one_mul] at hz
  linear_combination (norm := ring_nf) -hz
  norm_num [Complex.I_sq]
  dsimp [G,f,PositiveCircleGeometry.SmoothLift.angularStressPath,SmoothCircleFamily.toStressPath]
  ring
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Filter MeasureTheory Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.RealCircleCalculus
end StronglyRationalVOA.RealCircleCalculus

end

end OAI
