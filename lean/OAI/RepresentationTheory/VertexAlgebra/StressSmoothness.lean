import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.CoefficientSummableBound

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
namespace StronglyRationalVOA.RealCircleCalculus

lemma space_deriv_eq_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} (hf : Differentiable ℝ f) (p : ℝ × ℝ) :
    deriv (fun x => f (p.1,x)) p.2=fderiv ℝ f p (0,1) := by
  have hg : HasFDerivAt (fun x : ℝ => (p.1,x)) (ContinuousLinearMap.inr ℝ ℝ ℝ) p.2 := by
    convert (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) p.2) using 1 <;> rfl
  exact ((hf p).hasFDerivAt.comp p.2 hg).hasDerivAt.deriv
lemma time_deriv_eq_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} (hf : Differentiable ℝ f) (p : ℝ × ℝ) :
    deriv (fun t => f (t,p.2)) p.1=fderiv ℝ f p (1,0) := by
  have hg : HasFDerivAt (fun t : ℝ => (t,p.2)) (ContinuousLinearMap.inl ℝ ℝ ℝ) p.1 := by
    convert (hasFDerivAt_id (𝕜 := ℝ) p.1).prodMk (hasFDerivAt_const (𝕜 := ℝ) p.2 p.1) using 1 <;> rfl
  exact ((hf p).hasFDerivAt.comp p.1 hg).hasDerivAt.deriv
lemma space_deriv_smooth {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (fun x => f (p.1,x)) p.2) := by
  simp_rw [space_deriv_eq_fderiv (hf.differentiable (by simp))]
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
lemma time_deriv_smooth {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (fun t => f (t,p.2)) p.1) := by
  simp_rw [time_deriv_eq_fderiv (hf.differentiable (by simp))]
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
lemma mixed_deriv {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (t x : ℝ) :
    deriv (fun s => deriv (fun y => f (s,y)) x) t =
      deriv (fun y => deriv (fun s => f (s,y)) t) x := by
  have hd := hf.differentiable (by simp)
  have hh : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hdd := hh.differentiable (by simp)
  have hx (s : ℝ) := space_deriv_eq_fderiv hd (s,x)
  have ht (y : ℝ) := time_deriv_eq_fderiv hd (t,y)
  simp only at hx ht
  simp_rw [hx,ht]
  rw [time_deriv_eq_fderiv (hdd.clm_apply (differentiable_const (0,1))) (t,x),
    space_deriv_eq_fderiv (hdd.clm_apply (differentiable_const (1,0))) (t,x)]
  have he (v w : ℝ × ℝ) :
      fderiv ℝ (fun p => fderiv ℝ f p v) (t,x) w=fderiv ℝ (fderiv ℝ f) (t,x) w v := by
    have h := (hdd (t,x)).hasFDerivAt.clm_apply (hasFDerivAt_const v (t,x))
    rw [h.fderiv]
    simp
  rw [he,he]
  exact hf.contDiffAt.isSymmSndFDerivAt (by simp) _ _

 

lemma integral_derivative {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a b t : ℝ) :
    HasDerivAt (fun s => ∫ x in a..b, f (s,x))
      (∫ x in a..b, deriv (fun s => f (s,x)) t) t := by
  let G (s x : ℝ) := deriv (fun q => f (q,x)) s
  have hF (s : ℝ) : Continuous (fun x => f (s,x)) := hf.continuous.comp (continuous_const.prodMk continuous_id)
  have hG : Continuous (Function.uncurry G) := (time_deriv_smooth hf).continuous
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod isCompact_uIcc).exists_bound_of_continuousOn
    hG.continuousOn (s := Icc (t-1) (t+1) ×ˢ uIcc a b)
  have hd := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x => f (s,x)) (F' := G) (μ := volume) (a := a) (b := b)
    (s := Icc (t-1) (t+1)) (bound := fun _ => M)
    (Icc_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall (fun s => (hF s).aestronglyMeasurable))
    ((hF t).intervalIntegrable _ _)
    ((hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun x hx s hs => hM (s,x) ⟨hs,uIoc_subset_uIcc hx⟩))
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall (fun x _ s _ => by
      exact ((hf.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) s).hasDerivAt))
  exact hd.2
lemma periodic_deriv {g : ℝ → ℝ} {T : ℝ} (hp : Function.Periodic g T) :
    Function.Periodic (deriv g) T := by
  intro x
  have he : (fun y => g (y+T))=g := funext hp
  have h := congrFun (congrArg deriv he) x
  simpa only [deriv_comp_add_const] using h

def anomalyDensity (g : ℝ → ℝ) (x : ℝ) : ℝ := g x-(deriv g x)^2/g x

def anomalyFlux (g v : ℝ → ℝ) (x : ℝ) : ℝ :=
  v x*(deriv g x)^2/g x-v x*g x-2*g x*deriv (deriv v) x

def anomalyEnergy (T : ℝ) (g : ℝ → ℝ) : ℝ := ∫ x in 0..T, anomalyDensity g x

lemma anomaly_density_smooth {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hp : ∀ t x, g (t,x) ≠ 0) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => anomalyDensity (fun x => g (p.1,x)) p.2) :=
  hg.sub (((space_deriv_smooth hg).pow 2).div hg (fun p => hp p.1 p.2))

 

lemma anomaly_density_derivative {g v : ℝ × ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hv : ContDiff ℝ ∞ v) (hpos : ∀ t x, g (t,x) ≠ 0)
    (hpde : ∀ t x, deriv (fun s => g (s,x)) t =
      deriv (fun y => v (t,y)) x*g (t,x)-v (t,x)*deriv (fun y => g (t,y)) x)
    (t x : ℝ) :
    HasDerivAt (fun s => anomalyDensity (fun y => g (s,y)) x)
      (2*(deriv (deriv (deriv (fun y => v (t,y)))) x+deriv (fun y => v (t,y)) x)*g (t,x)+
        deriv (anomalyFlux (fun y => g (t,y)) (fun y => v (t,y))) x) t := by
  let G : ℝ → ℝ := fun y => g (t,y)
  let W : ℝ → ℝ := fun y => v (t,y)
  have hG : ContDiff ℝ ∞ G := hg.comp (contDiff_const.prodMk contDiff_id)
  have hW : ContDiff ℝ ∞ W := hv.comp (contDiff_const.prodMk contDiff_id)
  have hG' := (contDiff_infty_iff_deriv.mp hG).2
  have hW' := (contDiff_infty_iff_deriv.mp hW).2
  have hW'' := (contDiff_infty_iff_deriv.mp hW').2
  have hdx := (hG.differentiable (by simp) x).hasDerivAt
  have hdx' := (hG'.differentiable (by simp) x).hasDerivAt
  have hdv := (hW.differentiable (by simp) x).hasDerivAt
  have hdv' := (hW'.differentiable (by simp) x).hasDerivAt
  have hdv'' := (hW''.differentiable (by simp) x).hasDerivAt
  have hd := ((hg.comp (contDiff_id.prodMk (contDiff_const (c := x)))).differentiable (by simp) t).hasDerivAt
  change HasDerivAt (fun s => g (s,x)) (deriv (fun s => g (s,x)) t) t at hd
  rw [hpde] at hd
  have hsd := (((space_deriv_smooth hg).comp (contDiff_id.prodMk (contDiff_const (c := x)))).differentiable (by simp) t).hasDerivAt
  have he : (fun y => deriv (fun s => g (s,y)) t)=(fun y => deriv W y*G y-W y*deriv G y) :=
    funext (hpde t)
  have hm := mixed_deriv hg t x
  rw [he] at hm
  change _=deriv (deriv W*G-W*deriv G) x at hm
  rw [((hdv'.mul hdx).sub (hdv.mul hdx')).deriv] at hm
  change deriv (fun s => deriv (fun y => g (s,y)) x) t=_ at hm
  change HasDerivAt (fun s => deriv (fun y => g (s,y)) x)
    (deriv (fun s => deriv (fun y => g (s,y)) x) t) t at hsd
  rw [hm] at hsd
  have hdE := hd.sub ((hsd.pow 2).div hd (hpos t x))
  have hB := (((hdv.mul (hdx'.pow 2)).div hdx (hpos t x)).sub (hdv.mul hdx)).sub
    ((hdx.mul hdv'').const_mul 2)
  have heB : (fun y => W y*(deriv G y)^2/G y-W y*G y-2*(G y*deriv (deriv W) y))=
      anomalyFlux G W := by ext y; dsimp [anomalyFlux]; ring
  change HasDerivAt (fun y => W y*(deriv G y)^2/G y-W y*G y-2*(G y*deriv (deriv W) y)) _ x at hB
  rw [heB] at hB
  change HasDerivAt (fun s => anomalyDensity (fun y => g (s,y)) x)
    (2*(deriv (deriv (deriv W)) x+deriv W x)*G x+deriv (anomalyFlux G W) x) t
  rw [hB.deriv]
  convert hdE using 1 <;> try rfl
  simp only [G,W,Pi.pow_apply,Pi.mul_apply,Nat.cast_ofNat,show 2-1=1 from rfl,pow_one]
  field_simp [hpos t x]
  ring
lemma anomaly_flux_smooth {g v : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hv : ContDiff ℝ ∞ v)
    (hp : ∀ x, g x ≠ 0) : ContDiff ℝ ∞ (anomalyFlux g v) := by
  have hg' := (contDiff_infty_iff_deriv.mp hg).2
  have hv'' := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hv).2).2
  exact (((hv.mul (hg'.pow 2)).div hg hp).sub (hv.mul hg)).sub
    ((contDiff_const.mul hg).mul hv'')
lemma anomaly_flux_periodic {g v : ℝ → ℝ} {T : ℝ}
    (hg : Function.Periodic g T) (hv : Function.Periodic v T) :
    Function.Periodic (anomalyFlux g v) T := by
  intro x
  dsimp only [anomalyFlux]
  rw [hg,hv,periodic_deriv hg x,periodic_deriv (periodic_deriv hv) x]

lemma anomaly_energy_derivative {g v : ℝ × ℝ → ℝ} {T : ℝ}
    (hg : ContDiff ℝ ∞ g) (hv : ContDiff ℝ ∞ v) (hpos : ∀ t x, g (t,x) ≠ 0)
    (hgp : ∀ t, Function.Periodic (fun x => g (t,x)) T)
    (hvp : ∀ t, Function.Periodic (fun x => v (t,x)) T)
    (hpde : ∀ t x, deriv (fun s => g (s,x)) t =
      deriv (fun y => v (t,y)) x*g (t,x)-v (t,x)*deriv (fun y => g (t,y)) x)
    (t : ℝ) :
    HasDerivAt (fun s => anomalyEnergy T (fun y => g (s,y)))
      (2*∫ x in 0..T, (deriv (deriv (deriv (fun y => v (t,y)))) x+deriv (fun y => v (t,y)) x)*g (t,x)) t := by
  let G : ℝ → ℝ := fun y => g (t,y)
  let W : ℝ → ℝ := fun y => v (t,y)
  have hG : ContDiff ℝ ∞ G := hg.comp (contDiff_const.prodMk contDiff_id)
  have hW : ContDiff ℝ ∞ W := hv.comp (contDiff_const.prodMk contDiff_id)
  have hB := anomaly_flux_smooth hG hW (hpos t)
  have hBp := anomaly_flux_periodic (hgp t) (hvp t)
  have hB' := (contDiff_infty_iff_deriv.mp hB).2
  have hBI : (∫ x in 0..T, deriv (anomalyFlux G W) x)=0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => (hB.differentiable (by simp) x).hasDerivAt)
      (hB'.continuous.intervalIntegrable 0 T)]
    have he := hBp 0
    simpa only [zero_add,sub_eq_zero] using he
  have hW' := (contDiff_infty_iff_deriv.mp hW).2
  have hW''' := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hW').2).2
  have hC : Continuous (fun x => (deriv (deriv (deriv W)) x+deriv W x)*G x) :=
    (hW'''.continuous.add hW'.continuous).mul hG.continuous
  have hd := integral_derivative (anomaly_density_smooth hg hpos) 0 T t
  have he : (∫ x in 0..T, deriv (fun s => anomalyDensity (fun y => g (s,y)) x) t)=
      2*∫ x in 0..T, (deriv (deriv (deriv W)) x+deriv W x)*G x := by
    rw [intervalIntegral.integral_congr (fun x _ => (anomaly_density_derivative hg hv hpos hpde t x).deriv)]
    simp_rw [mul_assoc]
    change (∫ x in 0..T, 2*((deriv (deriv (deriv W)) x+deriv W x)*G x)+
      deriv (anomalyFlux G W) x)=_
    rw [intervalIntegral.integral_add ((hC.const_mul 2).intervalIntegrable 0 T)
      (hB'.continuous.intervalIntegrable 0 T),hBI,add_zero,intervalIntegral.integral_const_mul]
  exact he ▸ hd
end StronglyRationalVOA.RealCircleCalculus

open Filter MeasureTheory Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.RealCircleCalculus
lemma deriv_ofReal {g : ℝ → ℝ} (hg : Differentiable ℝ g) :
    deriv (fun x => (g x:ℂ))=fun x => ((deriv g x:ℝ):ℂ) :=
  funext fun x => (hg x).hasDerivAt.ofReal_comp.deriv
lemma iteratedDeriv_ofReal {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (k : ℕ) :
    iteratedDeriv k (fun x => (g x:ℂ))=fun x => ((iteratedDeriv k g x:ℝ):ℂ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ,ih,iteratedDeriv_succ]
    apply deriv_ofReal
    rw [iteratedDeriv_eq_iterate]
    exact (hg.iterate_deriv k).differentiable (by simp)
end StronglyRationalVOA.RealCircleCalculus
namespace StronglyRationalVOA.PositiveCircleGeometry.SmoothLift
variable (φ : SmoothLift)
def realAngularVelocity (p : ℝ × ℝ) : ℝ := 2*Real.pi*φ.velocity p.1 (p.2/(2*Real.pi))
def realAngularDensity (g : ℝ → ℝ) (k : ℕ) (p : ℝ × ℝ) : ℝ := φ.density g k p.1 (p.2/(2*Real.pi))
lemma realAngularVelocity_smooth : ContDiff ℝ ∞ φ.realAngularVelocity :=
  contDiff_const.mul (φ.velocity_smooth.comp (contDiff_fst.prodMk (contDiff_snd.div_const _)))
lemma realAngularDensity_smooth {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (k : ℕ) :
    ContDiff ℝ ∞ (φ.realAngularDensity g k) :=
  (φ.density_smooth hg k).comp (contDiff_fst.prodMk (contDiff_snd.div_const _))
lemma realAngularVelocity_periodic (t : ℝ) :
    Function.Periodic (fun x => φ.realAngularVelocity (t,x)) (2*Real.pi) := by
  intro x
  exact Complex.ofReal_injective ((φ.angularVelocity t).periodic x)
lemma realAngularDensity_periodic {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g 1)
    (k : ℕ) (t : ℝ) : Function.Periodic (fun x => φ.realAngularDensity g k (t,x)) (2*Real.pi) := by
  intro x
  exact Complex.ofReal_injective ((φ.angularDensity g hg hp k t).periodic x)
lemma realAngularDensity_pos {g : ℝ → ℝ} (hg : ∀ x, 0 < g x) (k : ℕ) (t x : ℝ) :
    0 < φ.realAngularDensity g k (t,x) :=
  mul_pos (pow_pos (φ.jacobian_pos _ _) _) (hg _)
lemma realAngularDensity_PDE {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g 1)
    (t x : ℝ) :
    deriv (fun s => φ.realAngularDensity g 1 (s,x)) t=
      deriv (fun y => φ.realAngularVelocity (t,y)) x*φ.realAngularDensity g 1 (t,x)-
      φ.realAngularVelocity (t,x)*deriv (fun y => φ.realAngularDensity g 1 (t,y)) x := by
  have hD : ContDiff ℝ ∞ (φ.realAngularDensity g 1) := φ.realAngularDensity_smooth hg 1
  have hV := φ.realAngularVelocity_smooth
  have he := congrArg (fun f : SmoothCircleFunction => f x) (φ.angularDensity_transport g hg hp 1 t)
  change deriv (fun s => ((φ.realAngularDensity g 1 (s,x)):ℂ)) t=_ at he
  rw [SmoothCircleFunction.primaryTransport_apply] at he
  change _ = ((2:ℂ)-1)*deriv (fun y => ((φ.realAngularVelocity (t,y)):ℂ)) x*
      ((φ.realAngularDensity g 1 (t,x)):ℂ)-
      ((φ.realAngularVelocity (t,x)):ℂ)*deriv (fun y => ((φ.realAngularDensity g 1 (t,y)):ℂ)) x at he
  rw [RealCircleCalculus.deriv_ofReal (g := fun s => φ.realAngularDensity g 1 (s,x)) ((hD.comp (contDiff_id.prodMk (contDiff_const (c := x)))).differentiable (by simp)),
    RealCircleCalculus.deriv_ofReal (g := fun y => φ.realAngularVelocity (t,y)) ((hV.comp ((contDiff_const (c := t)).prodMk contDiff_id)).differentiable (by simp)),
    RealCircleCalculus.deriv_ofReal (g := fun y => φ.realAngularDensity g 1 (t,y)) ((hD.comp ((contDiff_const (c := t)).prodMk contDiff_id)).differentiable (by simp))] at he
  apply Complex.ofReal_injective
  push_cast
  norm_num only [show (2:ℂ)-1=1 from by norm_num,one_mul] at he
  exact he
lemma angular_cocycle_coefficient {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g 1)
    (t : ℝ) :
    ((φ.angularVelocity t).cocycleDensity (φ.angularDensity g hg hp 1 t)).coefficient 0 =
      ((2*Real.pi)⁻¹*(∫ x in 0..2*Real.pi,
        (deriv (deriv (deriv (fun y => φ.realAngularVelocity (t,y)))) x+
          deriv (fun y => φ.realAngularVelocity (t,y)) x)*φ.realAngularDensity g 1 (t,x)):ℝ) := by
  let v : ℝ → ℝ := fun x => φ.realAngularVelocity (t,x)
  let G : ℝ → ℝ := fun x => φ.realAngularDensity g 1 (t,x)
  have hv : ContDiff ℝ ∞ v := φ.realAngularVelocity_smooth.comp (contDiff_const.prodMk contDiff_id)
  have he : (fun x => (φ.angularVelocity t).cocycleDensity (φ.angularDensity g hg hp 1 t) x)=
      fun x => (((deriv (deriv (deriv v)) x+deriv v x)*G x:ℝ):ℂ) := by
    funext x
    simp only [SmoothCircleFunction.cocycleDensity,SmoothCircleFunction.mul_apply,
      SmoothCircleFunction.add_apply,SmoothCircleFunction.differentiated_apply]
    change (iteratedDeriv 3 (fun x => (v x:ℂ)) x+iteratedDeriv 1 (fun x => (v x:ℂ)) x)*(G x:ℂ)=_
    rw [RealCircleCalculus.iteratedDeriv_ofReal hv,RealCircleCalculus.iteratedDeriv_ofReal hv]
    simp only [iteratedDeriv_succ,iteratedDeriv_zero,Complex.ofReal_add,Complex.ofReal_mul]
  rw [SmoothCircleFunction.coefficient,fourierCoeffOn_eq_integral]
  simp only [neg_zero,fourier_zero,one_smul]
  rw [he]
  rw [intervalIntegral.integral_ofReal]
  simp [Complex.real_smul,v,G,one_div]

 
def normalizedAnomaly (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  (2*Real.pi)⁻¹*RealCircleCalculus.anomalyEnergy (2*Real.pi)
    (fun x => φ.realAngularDensity g 1 (t,x))
def anomalyShift (g : ℝ → ℝ) (c : ℂ) (t : ℝ) : ℂ :=
  c/24*((φ.normalizedAnomaly g t-φ.normalizedAnomaly g 0):ℝ)
@[simp] lemma anomalyShift_zero (g : ℝ → ℝ) (c : ℂ) : φ.anomalyShift g c 0=0 := by
  simp [anomalyShift]
lemma anomalyShift_derivative {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g 1)
    (hpos : ∀ x, 0 < g x) (c : ℂ) (t : ℝ) :
    HasDerivAt (φ.anomalyShift g c)
      (c/12*((φ.angularVelocity t).cocycleDensity (φ.angularDensity g hg hp 1 t)).coefficient 0) t := by
  have hd := RealCircleCalculus.anomaly_energy_derivative (φ.realAngularDensity_smooth hg 1)
    φ.realAngularVelocity_smooth (fun t x => ne_of_gt (φ.realAngularDensity_pos hpos 1 t x))
    (φ.realAngularDensity_periodic hg hp 1) φ.realAngularVelocity_periodic
    (φ.realAngularDensity_PDE hg hp) t
  have he := (((hd.const_mul ((2*Real.pi)⁻¹)).sub_const (φ.normalizedAnomaly g 0)).ofReal_comp).const_mul (c/24)
  rw [φ.angular_cocycle_coefficient hg hp t]
  convert he using 1 <;> try rfl
  push_cast
  ring
end StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

open Filter MeasureTheory Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.PositiveCircleGeometry.Field
variable (f : Field (2*Real.pi))
def unitParameter (x : ℝ) : ℝ := f (2*Real.pi*x)
lemma unitParameter_smooth : ContDiff ℝ ∞ f.unitParameter :=
  f.smooth.comp (contDiff_const.mul contDiff_id)
lemma unitParameter_periodic : Function.Periodic f.unitParameter 1 := by
  intro x
  dsimp only [unitParameter]
  rw [mul_add,mul_one,f.periodic]
lemma unitParameter_pos (x : ℝ) : 0 < f.unitParameter x := f.positive _
def flattening : SmoothLift where
  toFun := f.normalizedCoordinate
  add_one := f.coordinate_add_one SmoothCircleFunction.period_pos
  smooth := f.coordinate_smooth
  derivative_pos := fun x => by
    rw [(f.coordinate_hasDerivAt x).deriv]
    exact f.coordinate_derivative_pos SmoothCircleFunction.period_pos x
lemma flattening_density_one (x : ℝ) : f.flattening.density f.unitParameter 1 1 x=f.frequency := by
  change f.flattening.jacobian 1 (f.flattening.inverse 1 x)^1*f.unitParameter (f.flattening.inverse 1 x)=_
  simp only [SmoothLift.jacobian,Real.smoothTransition.one,pow_one,sub_self,zero_add,one_mul]
  exact f.flatten_identity SmoothCircleFunction.period_pos _
lemma flattening_realDensity_zero (x : ℝ) : f.flattening.realAngularDensity f.unitParameter 1 (0,x)=f x := by
  change f.flattening.density f.unitParameter 1 0 (x/(2*Real.pi))=f x
  rw [SmoothLift.density_zero]
  dsimp only [unitParameter]
  congr 1
  field_simp [Real.pi_ne_zero]
lemma flattening_realDensity_one (x : ℝ) : f.flattening.realAngularDensity f.unitParameter 1 (1,x)=f.frequency :=
  f.flattening_density_one _
lemma flatteningAnomaly_one : f.flattening.normalizedAnomaly f.unitParameter 1=f.frequency := by
  unfold SmoothLift.normalizedAnomaly RealCircleCalculus.anomalyEnergy
  have he : (fun x => f.flattening.realAngularDensity f.unitParameter 1 (1,x))=fun _ => f.frequency :=
    funext f.flattening_realDensity_one
  rw [he]
  simp only [RealCircleCalculus.anomalyDensity,deriv_const,zero_pow (by decide : 2≠0),zero_div,sub_zero,
    intervalIntegral.integral_const,smul_eq_mul,sub_zero]
  field_simp [Real.pi_ne_zero]
lemma flatteningAnomaly_zero : f.flattening.normalizedAnomaly f.unitParameter 0=
    (2*Real.pi)⁻¹*((∫ x in 0..2*Real.pi, f x)-(∫ x in 0..2*Real.pi, (deriv f x)^2/f x)) := by
  unfold SmoothLift.normalizedAnomaly RealCircleCalculus.anomalyEnergy
  have he : (fun x => f.flattening.realAngularDensity f.unitParameter 1 (0,x))=f :=
    funext f.flattening_realDensity_zero
  rw [he]
  dsimp only [RealCircleCalculus.anomalyDensity]
  congr 1
  exact intervalIntegral.integral_sub (f.smooth.continuous.intervalIntegrable _ _)
    ((((contDiff_infty_iff_deriv.mp f.smooth).2.continuous.pow 2).div f.smooth.continuous
      (fun x => ne_of_gt (f.positive x))).intervalIntegrable _ _)
lemma flatteningShift (c : ℝ) : f.flattening.anomalyShift f.unitParameter (c:ℂ) 1=(-(f.stressScalar c):ℝ) := by
  rw [SmoothLift.anomalyShift,f.flatteningAnomaly_one,f.flatteningAnomaly_zero]
  dsimp only [stressScalar]
  push_cast
  ring
end StronglyRationalVOA.PositiveCircleGeometry.Field
namespace StronglyRationalVOA.PositiveCircleGeometry.SmoothLift
variable (φ : SmoothLift)
lemma density_power (g : ℝ → ℝ) (k : ℕ) (t x : ℝ) :
    φ.density (fun x => g x^k) k t x=(φ.density g 1 t x)^k := by
  simp only [density,pow_one,mul_pow]
end StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

open UniformSpace Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction
def constant (c : ℂ) : SmoothCircleFunction where
  toFun := fun _ => c
  periodic := fun _ => rfl
  smooth := contDiff_const
@[simp] lemma constant_apply (c : ℂ) (x : ℝ) : constant c x=c := rfl
lemma coefficient_constant_zero (c : ℂ) : (constant c).coefficient 0=c := by
  rw [coefficient,fourierCoeffOn_eq_integral]
  simp only [neg_zero,fourier_zero,one_smul,constant_apply,intervalIntegral.integral_const,sub_zero]
  simp only [Complex.real_smul]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
lemma coefficient_zero_constant (n : ℤ) : (constant 0).coefficient n=0 := by
  simp [coefficient,fourierCoeffOn_eq_integral,constant]
lemma coefficient_constant (c : ℂ) (n : ℤ) : (constant c).coefficient n=if n=0 then c else 0 := by
  by_cases hn : n=0
  · subst n; simp [coefficient_constant_zero]
  · rw [ite_eq_right hn]
    have hd := coefficient_differentiated (constant c) 1 n
    have he : (constant c).differentiated 1=constant 0 := by
      apply ext; intro x
      simp only [differentiated_apply,iteratedDeriv_one,constant_apply]
      exact deriv_const x c
    rw [he,coefficient_zero_constant,pow_one] at hd
    exact (mul_eq_zero.mp hd.symm).resolve_left (mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hn))
end StronglyRationalVOA.SmoothCircleFunction
namespace StronglyRationalVOA.CFTTypeVOA
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (A : CFTTypeVOA V)
lemma smearedMap_constant (a : V) (d : ℕ) (ha : A.PolynomialEnergyBound a) (c : ℂ) (v : V) :
    A.smearedMap a d ha (SmoothCircleFunction.constant c).coefficient
      (SmoothCircleFunction.constant c).rapid_coefficients v=c • (A.physicalMode a d 0 v:Completion V) := by
  rw [smearedMap_apply]
  simp only [SmoothCircleFunction.coefficient_constant,ite_smul,zero_smul]
  rw [tsum_eq_single (0:ℤ) (fun n hn => by simp only [ite_eq_right hn]),ite_eq_left rfl]
end StronglyRationalVOA.CFTTypeVOA
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma smooth_constant_bound (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d k : ℕ} (ha : a ∈ A.grade d) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ v, ‖A.physicalMode a d 0 v‖ ≤ C*‖(A.energyShift^k) v‖)
    (x : U.smoothEnergySpace) :
    ‖(U.smoothSmear hc ha (SmoothCircleFunction.constant 1).rapid_coefficients x:Completion V)‖ ≤
      C*‖U.smoothEnergyPower k x‖ := by
  have hM : ∀ v, ‖A.smearedMap a d (U.polynomialEnergyBounds hc a)
      (SmoothCircleFunction.constant 1).coefficient (SmoothCircleFunction.constant 1).rapid_coefficients v‖ ≤
      C*‖(A.energyShift^k) v‖ := by
    intro v
    simpa only [A.smearedMap_constant,one_smul,Completion.norm_coe] using hb v
  rw [U.smoothSmear_eq_extension hc ha _ hM x (U.smoothEnergyPower_graph k x)]
  exact (U.sobolevExtension k _).le_of_opNorm_le (U.sobolevExtension_norm k _ hC hM) _
lemma constant_stress_core (hc : A.toVertexAlgebra.C2Cofinite) (v : V) :
    A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector)
      (SmoothCircleFunction.constant 1).coefficient (SmoothCircleFunction.constant 1).rapid_coefficients v=
      (A.virasoroMode 0 v:Completion V) := by
  rw [A.smearedMap_constant,one_smul]
  rfl
lemma constant_stress_bound (hc : A.toVertexAlgebra.C2Cofinite) (v : V) :
    ‖A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector)
      (SmoothCircleFunction.constant 1).coefficient (SmoothCircleFunction.constant 1).rapid_coefficients v‖ ≤
      (1+A.centralCharge.re)*‖A.energyShift v‖ := by
  rw [U.constant_stress_core hc,Completion.norm_coe]
  simpa only [Int.cast_zero,abs_zero,add_zero,one_pow,mul_one] using U.virasoro_linear_energy 0 v
lemma constant_stress_extension (hc : A.toVertexAlgebra.C2Cofinite) :
    U.sobolevExtension 1 (A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector)
      (SmoothCircleFunction.constant 1).coefficient (SmoothCircleFunction.constant 1).rapid_coefficients)=
    1-U.inverseSobolev 1 := by
  have hb (v : V) := U.constant_stress_bound hc v
  have hb' : ∀ v, ‖A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector)
      (SmoothCircleFunction.constant 1).coefficient (SmoothCircleFunction.constant 1).rapid_coefficients v‖ ≤
      (1+A.centralCharge.re)*‖(A.energyShift^1) v‖ := by simpa only [pow_one] using hb
  apply ContinuousLinearMap.ext
  intro x
  refine Completion.denseRange_coe.induction_on x ?_ ?_
  · exact isClosed_eq (U.sobolevExtension 1 _).continuous (1-U.inverseSobolev 1).continuous
  · intro v
    rw [U.sobolevExtension_coe 1 _ hb',U.constant_stress_core hc]
    change (A.virasoroMode 0 (U.inverseCoreEnergy 1 v):Completion V)=(v:Completion V)-U.inverseSobolev 1 v
    rw [← U.inverseCoreEnergy_coe,← Completion.coe_sub]
    congr 1
    have he := U.energyShift_inverseCoreEnergy 1 v
    change U.inverseCoreEnergy 1 v+A.virasoroMode 0 (U.inverseCoreEnergy 1 v)=v at he
    exact eq_sub_of_add_eq' he
lemma smoothEnergyPower_one_constant_stress (hc : A.toVertexAlgebra.C2Cofinite) (x : U.smoothEnergySpace) :
    U.smoothEnergyPower 1 x=(x:Completion V)+
      (U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.constant 1).rapid_coefficients x:Completion V) := by
  have hb' : ∀ v, ‖A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector)
      (SmoothCircleFunction.constant 1).coefficient (SmoothCircleFunction.constant 1).rapid_coefficients v‖ ≤
      (1+A.centralCharge.re)*‖(A.energyShift^1) v‖ := by simpa only [pow_one] using U.constant_stress_bound hc
  rw [U.smoothSmear_eq_extension hc A.conformal_mem _ hb' x (U.smoothEnergyPower_graph 1 x),
    U.constant_stress_extension hc]
  change _=(x:Completion V)+(U.smoothEnergyPower 1 x-U.inverseSobolev 1 (U.smoothEnergyPower 1 x))
  rw [U.inverseSobolev_smoothEnergyPower]
  abel
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Filter UniformSpace
open scoped Topology ContDiff
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
@[simp] lemma stressPropagatorSmooth_zero (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (y : U.smoothEnergySpace) : U.stressPropagatorSmooth hc f 0 y=y := by
  apply Subtype.ext
  change U.stressPropagator hc f 0 y=(y:Completion V)
  rw [U.stressPropagator_zero hc f,one_apply_eq_self]
lemma stress_density_form_covariance (hc : A.toVertexAlgebra.C2Cofinite)
    (φ : PositiveCircleGeometry.SmoothLift) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : Function.Periodic g 1) (hpos : ∀ x, 0 < g x) (t : ℝ) (x y : U.smoothEnergySpace) :
    inner ℂ (U.stressPropagator hc φ.angularStressPath t x)
      (U.smoothSmear hc A.conformal_mem (φ.angularDensity g hg hp 1 t).rapid_coefficients
        (U.stressPropagatorSmooth hc φ.angularStressPath t y) : Completion V)=
    inner ℂ (x:Completion V)
      (U.smoothSmear hc A.conformal_mem (φ.angularDensity g hg hp 1 0).rapid_coefficients y : Completion V)+
      φ.anomalyShift g A.centralCharge t*inner ℂ (x:Completion V) (y:Completion V) := by
  let F : ℝ → ℂ := fun s => inner ℂ (U.stressPropagator hc φ.angularStressPath s x)
      (U.smoothSmear hc A.conformal_mem (φ.angularDensity g hg hp 1 s).rapid_coefficients
        (U.stressPropagatorSmooth hc φ.angularStressPath s y) : Completion V)-
      φ.anomalyShift g A.centralCharge s*inner ℂ (x:Completion V) (y:Completion V)
  have hd (s : ℝ) : HasDerivAt F 0 s := by
    have h := (U.stress_density_form_derivative hc φ g hg hp s x y).sub
      ((φ.anomalyShift_derivative hg hp hpos A.centralCharge s).mul_const
        (inner ℂ (x:Completion V) (y:Completion V)))
    convert h using 1
    first | rfl | simp only [sub_self]
  have he := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  dsimp only [F] at he
  simp only [φ.anomalyShift_zero,zero_mul,sub_zero,U.stressPropagatorSmooth_zero,
    U.stressPropagator_zero,one_apply_eq_self] at he
  exact sub_eq_iff_eq_add.mp he
lemma stress_density_smooth_covariance (hc : A.toVertexAlgebra.C2Cofinite)
    (φ : PositiveCircleGeometry.SmoothLift) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : Function.Periodic g 1) (hpos : ∀ x, 0 < g x) (t : ℝ) (y : U.smoothEnergySpace) :
    (U.smoothSmear hc A.conformal_mem (φ.angularDensity g hg hp 1 t).rapid_coefficients
      (U.stressPropagatorSmooth hc φ.angularStressPath t y) : Completion V)=
    U.stressPropagator hc φ.angularStressPath t
      (U.smoothSmear hc A.conformal_mem (φ.angularDensity g hg hp 1 0).rapid_coefficients y : Completion V)+
      φ.anomalyShift g A.centralCharge t • U.stressPropagator hc φ.angularStressPath t y := by
  let E := U.stressPropagatorEquiv hc φ.angularStressPath t
  apply E.symm.injective
  apply ext_inner_left ℂ
  intro z
  refine U.smoothEnergySpace_dense.denseRange_val.induction_on z ?_ ?_
  · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  · intro w
    have h := U.stress_density_form_covariance hc φ g hg hp hpos t w y
    have hi := E.inner_map_map (w:Completion V)
      (E.symm (U.smoothSmear hc A.conformal_mem (φ.angularDensity g hg hp 1 t).rapid_coefficients
        (U.stressPropagatorSmooth hc φ.angularStressPath t y)))
    rw [E.apply_symm_apply] at hi
    change inner ℂ (w:Completion V)
        (E.symm (U.smoothSmear hc A.conformal_mem (φ.angularDensity g hg hp 1 t).rapid_coefficients
          (U.stressPropagatorSmooth hc φ.angularStressPath t y))) =
      inner ℂ (w:Completion V) (E.symm (E (U.smoothSmear hc A.conformal_mem
        (φ.angularDensity g hg hp 1 0).rapid_coefficients y)+φ.anomalyShift g A.centralCharge t • E y))
    rw [map_add,map_smul,E.symm_apply_apply,E.symm_apply_apply,inner_add_right,inner_smul_right]
    exact hi.symm.trans h
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
