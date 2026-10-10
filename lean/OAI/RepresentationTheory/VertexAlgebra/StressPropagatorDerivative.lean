import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.StressCutoffNormalized2

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
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma stressPropagatorDerivative_smoothSmear (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (t : ℝ) (x : U.smoothEnergySpace) :
    U.stressPropagatorDerivative hc f t x=Complex.I •
      (U.smoothSmear hc A.conformal_mem (f.rapid t) (U.stressPropagatorSmooth hc f t x) : Completion V) := by
  have he := (U.closedSmearedOperator hc A.conformalVector 2 (f.coefficients t) (f.rapid t)).mem_graph_snd_inj
    (U.stressPropagatorDerivative_graph hc f t x)
    (U.smoothSmear_graph hc A.conformal_mem (f.rapid t) (U.stressPropagatorSmooth hc f t x)) rfl
  have h := congrArg (fun v : Completion V => Complex.I • v) he
  simpa only [smul_smul,mul_neg,Complex.I_mul_I,neg_neg,one_smul] using h

 

lemma smoothSmear_form_derivative (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d p k : ℕ} (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    {g : ℝ → ℤ → ℂ} (hg : ∀ t, RapidCoefficients (g t)) {h : ℤ → ℂ} (hr : RapidCoefficients h)
    (t : ℝ) (hgr : ∀ n, star (g t n)=g t (-n))
    (hl : Tendsto (fun s => coefficientSeminorm
      (fun n => (((s-t)⁻¹:ℝ):ℂ)*(g s n-g t n)-h n) p) (𝓝[≠] t) (𝓝 0))
    (x y : ℝ → U.smoothEnergySpace) (dx dy : Completion V)
    (hx : HasDerivAt (fun s => (x s : Completion V)) dx t)
    (hy : HasDerivAt (fun s => (y s : Completion V)) dy t)
    (hyc : ContinuousAt (fun s => U.smoothEnergyPower k (y s)) t) :
    HasDerivAt (fun s => inner ℂ (x s : Completion V) (U.smoothSmear hc ha (hg s) (y s) : Completion V))
      (inner ℂ dx (U.smoothSmear hc ha (hg t) (y t) : Completion V)+
        inner ℂ (U.smoothSmear hc ha (hg t) (x t) : Completion V) dy+
        inner ℂ (x t : Completion V) (U.smoothSmear hc ha hr (y t) : Completion V)) t := by
  let P (s : ℝ) : U.smoothEnergySpace →ₗ[ℂ] Completion V :=
    U.smoothEnergySpace.subtype.comp (U.smoothSmear hc ha (hg s))
  have hd := U.normalizedField_derivative hc hC hb hg hr t hl
  have hPy : ContinuousAt (fun s => P s (y s)) t := by
    have hc' := hd.continuousAt.clm_apply hyc
    simpa only [P,LinearMap.comp_apply,Submodule.subtype_apply,
      U.smoothSmear_eq_normalized hc ha hb] using hc'
  have hP : Tendsto (fun s => (s-t)⁻¹ • (P s (y s)-P t (y s))) (𝓝[≠] t)
      (𝓝 (U.smoothSmear hc ha hr (y t) : Completion V)) := by
    have he (s : ℝ) : (s-t)⁻¹ • (P s (y s)-P t (y s))=
        slope (fun q => U.normalizedField hc a d k (hg q)) t s (U.smoothEnergyPower k (y s)) := by
      dsimp only [P,LinearMap.comp_apply,Submodule.subtype_apply]
      rw [U.smoothSmear_eq_normalized hc ha hb,U.smoothSmear_eq_normalized hc ha hb]
      simp only [slope,vsub_eq_sub,smul_apply,sub_apply]
    have ht := (isBoundedBilinearMap_apply (𝕜 := ℂ)).continuous.tendsto
      (U.normalizedField hc a d k hr,U.smoothEnergyPower k (y t)) |>.comp
      (hd.tendsto_slope.prodMk_nhds (hyc.mono_left nhdsWithin_le_nhds))
    simpa only [Function.comp_def,← he,← U.smoothSmear_eq_normalized hc ha hb] using ht
  exact SymmetricOperator.form_pairing_derivative U.smoothEnergySpace P x y t dx dy
    (U.smoothSmear hc ha hr (y t)) (U.smoothSmear_symmetric hc ha hq hh (hg t) hgr) hx hy hPy hP
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.OperatorTransport
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma onSubmodule (E : H ≃ₗᵢ[ℂ] H) (D : Submodule ℂ H) (P Q : Module.End ℂ D)
    (hE : ∀ x ∈ D, E x ∈ D) (hI : ∀ x ∈ D, E.symm x ∈ D)
    (hc : ∀ x : D, (Q ⟨E x,hE x x.property⟩ : H)=E (P x)) :
    transport E (SymmetricOperator.onSubmodule D Q)=SymmetricOperator.onSubmodule D P := by
  apply LinearPMap.eq_of_eq_graph
  ext p
  rw [mem_graph_iff]
  constructor
  · intro hp
    obtain ⟨z,hz,hQ⟩ := (LinearPMap.mem_graph_iff _).mp hp
    let w : D := ⟨E.symm z,hI z z.property⟩
    have hw : (w:H)=p.1 := by change E.symm (z:H)=p.1; rw [hz,E.symm_apply_apply]
    have hzw : (⟨E w,hE w w.property⟩ : D)=z := Subtype.ext (E.apply_symm_apply z)
    have hPw : (P w:H)=p.2 := by
      apply E.injective
      rw [← hc w,hzw]
      exact hQ
    exact (LinearPMap.mem_graph_iff _).mpr ⟨w,hw,hPw⟩
  · intro hp
    obtain ⟨w,hw,hP⟩ := (LinearPMap.mem_graph_iff _).mp hp
    refine (LinearPMap.mem_graph_iff _).mpr ⟨⟨E w,hE w w.property⟩,?_,?_⟩
    · exact congrArg E hw
    · change (Q ⟨E w,hE w w.property⟩:H)=E p.2
      change (P w:H)=p.2 at hP
      rw [hc w,hP]
end StronglyRationalVOA.OperatorTransport

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma stressPropagator_zero (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath) :
    U.stressPropagator hc f 0=1 := by
  ext x
  apply tendsto_nhds_unique (U.stressPropagator_limit hc f 0 x)
  simpa only [TimeOrdered.evolution_zero,one_apply_eq_self] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))

lemma primary_transport_form_derivative (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a) (hh : U.IsHermitian d a)
    (f : StressPath) {g : ℝ → ℤ → ℂ} (hg : ∀ t, RapidCoefficients (g t))
    {h : ℤ → ℂ} (hr : RapidCoefficients h) (t : ℝ)
    (hgr : ∀ n, star (g t n)=g t (-n))
    (hl : ∀ p, Tendsto (fun s => coefficientSeminorm
      (fun n => (((s-t)⁻¹:ℝ):ℂ)*(g s n-g t n)-h n) p) (𝓝[≠] t) (𝓝 0))
    (hconv : ∀ r : ℤ, HasSum (fun m : ℤ => (((d:ℂ)-1)*m-(r-m))*f.coefficients t m*g t (r-m)) (-Complex.I*h r))
    (x y : U.smoothEnergySpace) :
    HasDerivAt (fun s => inner ℂ (U.stressPropagator hc f s x)
      (U.smoothSmear hc ha (hg s) (U.stressPropagatorSmooth hc f s y) : Completion V)) 0 t := by
  obtain ⟨C,hC,p,k,hb⟩ := (U.polynomialEnergyBounds hc a).physical A d
  have hd := U.smoothSmear_form_derivative hc ha (hp 1 (by norm_num)) hh (le_of_lt hC) hb hg hr t hgr (hl p)
    (fun s => U.stressPropagatorSmooth hc f s x) (fun s => U.stressPropagatorSmooth hc f s y)
    _ _ (U.stressPropagator_derivative hc f t x) (U.stressPropagator_derivative hc f t y)
    (U.stressPropagatorSmooth_continuous_power hc f k y).continuousAt
  have hw := U.primary_stress_smoothCommutator hc ha hp hh (f.rapid t) (hg t) hr
    (f.real t) hgr hconv (U.stressPropagatorSmooth hc f t x) (U.stressPropagatorSmooth hc f t y)
  rw [U.stressPropagatorDerivative_smoothSmear hc f t x,
    U.stressPropagatorDerivative_smoothSmear hc f t y,
    inner_smul_left,inner_smul_right,Complex.conj_I] at hd
  have hz := congrArg (fun z : ℂ => -Complex.I*z) hw
  simp only [neg_mul_neg,← mul_assoc,Complex.I_mul_I,neg_one_mul] at hz
  have he : -Complex.I * inner ℂ
        (U.smoothSmear hc A.conformal_mem (f.rapid t) (U.stressPropagatorSmooth hc f t x) : Completion V)
        (U.smoothSmear hc ha (hg t) (U.stressPropagatorSmooth hc f t y) : Completion V) +
      Complex.I * inner ℂ
        (U.smoothSmear hc ha (hg t) (U.stressPropagatorSmooth hc f t x) : Completion V)
        (U.smoothSmear hc A.conformal_mem (f.rapid t) (U.stressPropagatorSmooth hc f t y) : Completion V) +
      inner ℂ (U.stressPropagatorSmooth hc f t x : Completion V)
        (U.smoothSmear hc ha hr (U.stressPropagatorSmooth hc f t y) : Completion V)=0 := by
    linear_combination hz
  rw [he] at hd
  exact hd

 
lemma primary_transport_form_constant (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a) (hh : U.IsHermitian d a)
    (f : StressPath) {g h : ℝ → ℤ → ℂ} (hg : ∀ t, RapidCoefficients (g t))
    (hr : ∀ t, RapidCoefficients (h t)) {S : Set ℝ} (hS : Convex ℝ S) (h0 : 0 ∈ S)
    (hgr : ∀ t ∈ S, ∀ n, star (g t n)=g t (-n))
    (hl : ∀ t ∈ S, ∀ p, Tendsto (fun s => coefficientSeminorm
      (fun n => (((s-t)⁻¹:ℝ):ℂ)*(g s n-g t n)-h t n) p) (𝓝[≠] t) (𝓝 0))
    (hconv : ∀ t ∈ S, ∀ r : ℤ, HasSum (fun m : ℤ => (((d:ℂ)-1)*m-(r-m))*f.coefficients t m*g t (r-m)) (-Complex.I*h t r))
    {t : ℝ} (ht : t ∈ S) (x y : U.smoothEnergySpace) :
    inner ℂ (U.stressPropagator hc f t x)
      (U.smoothSmear hc ha (hg t) (U.stressPropagatorSmooth hc f t y) : Completion V)=
    inner ℂ (x : Completion V) (U.smoothSmear hc ha (hg 0) y : Completion V) := by
  have hd (s : ℝ) (hs : s ∈ S) := U.primary_transport_form_derivative hc ha hp hh f hg (hr s)
    s (hgr s hs) (hl s hs) (hconv s hs) x y
  have he := hS.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hd s hs).hasDerivWithinAt) (fun _ _ => (norm_zero : ‖(0:ℂ)‖=0).le) h0 ht
  have hz : U.stressPropagatorSmooth hc f 0 y=y := by
    apply Subtype.ext
    change U.stressPropagator hc f 0 y=(y:Completion V)
    rw [U.stressPropagator_zero hc f,one_apply_eq_self]
  simpa only [zero_mul,norm_le_zero_iff,sub_eq_zero,U.stressPropagator_zero hc f,one_apply_eq_self,hz] using he

def stressPropagatorEquiv (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath) (t : ℝ) :
    Completion V ≃ₗᵢ[ℂ] Completion V :=
  Unitary.linearIsometryEquiv ⟨U.stressPropagator hc f t,U.stressPropagator_unitary hc f t⟩

lemma stressPropagatorEquiv_apply (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath) (t : ℝ) (x : Completion V) :
    U.stressPropagatorEquiv hc f t x=U.stressPropagator hc f t x := rfl

lemma stressPropagatorEquiv_symm_apply (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath) (t : ℝ) (x : Completion V) :
    (U.stressPropagatorEquiv hc f t).symm x=star (U.stressPropagator hc f t) x := rfl

 
lemma primary_transport_smooth_covariance (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (f : StressPath) {g h : ℤ → ℂ} (hg : RapidCoefficients g) (hh : RapidCoefficients h) (t : ℝ)
    (he : ∀ x y : U.smoothEnergySpace,
      inner ℂ (U.stressPropagator hc f t x)
        (U.smoothSmear hc ha hh (U.stressPropagatorSmooth hc f t y) : Completion V)=
      inner ℂ (x:Completion V) (U.smoothSmear hc ha hg y : Completion V))
    (y : U.smoothEnergySpace) :
    (U.smoothSmear hc ha hh (U.stressPropagatorSmooth hc f t y) : Completion V)=
      U.stressPropagator hc f t (U.smoothSmear hc ha hg y : Completion V) := by
  let E := U.stressPropagatorEquiv hc f t
  apply E.symm.injective
  apply ext_inner_left ℂ
  intro z
  refine U.smoothEnergySpace_dense.denseRange_val.induction_on z ?_ ?_
  · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  · intro w
    have h := he w y
    have hi := E.inner_map_map (w:Completion V)
      (E.symm (U.smoothSmear hc ha hh (U.stressPropagatorSmooth hc f t y)))
    rw [E.apply_symm_apply] at hi
    change inner ℂ (w:Completion V) (E.symm (U.smoothSmear hc ha hh (U.stressPropagatorSmooth hc f t y))) =
      inner ℂ (w:Completion V) (E.symm (E (U.smoothSmear hc ha hg y)))
    rw [E.symm_apply_apply]
    exact hi.symm.trans h
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

lemma stress_transport_closed_graph (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (f : StressPath) {g h : ℤ → ℂ} (hg : RapidCoefficients g) (hh : RapidCoefficients h) (t : ℝ)
    (he : ∀ y : U.smoothEnergySpace,
      (U.smoothSmear hc ha hh (U.stressPropagatorSmooth hc f t y) : Completion V)=
      U.stressPropagator hc f t (U.smoothSmear hc ha hg y : Completion V)) :
    OperatorTransport.transport (U.stressPropagatorEquiv hc f t)
      (U.closedSmearedOperator hc a d h hh)=U.closedSmearedOperator hc a d g hg := by
  rw [← U.smoothSmear_core hc ha hh,← U.smoothSmear_core hc ha hg,
    ← OperatorTransport.closure _ (U.smoothSmear_core_closable hc ha hh)]
  congr 1
  exact OperatorTransport.onSubmodule _ _ _ _
    (fun x hx => U.stressPropagator_smooth hc f t hx)
    (fun x hx => U.stressPropagator_star_smooth hc f t hx) he
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.PositiveCircleGeometry
 

lemma parameter_inverse_smooth (F : ℝ → ℝ ≃o ℝ)
    (hF : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2))
    (hn : ∀ t y, deriv (F t) y ≠ 0) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => (F p.1).symm p.2) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  let y : ℝ := (F p.1).symm p.2
  let K : (ℝ × ℝ) × ℝ → ℝ := fun q => F q.1.1 q.2-q.1.2
  have hK : ContDiff ℝ ∞ K :=
    (hF.comp (contDiff_fst.fst.prodMk contDiff_snd)).sub contDiff_fst.snd
  let L := fderiv ℝ K (p,y)
  have hpart : HasDerivAt (fun z => F p.1 z-p.2)
      ((L.comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ)) 1) y := by
    have hd := (hK.differentiable (by simp) (p,y)).hasFDerivAt
    have hcomp := hd.comp y ((hasFDerivAt_const (p : ℝ × ℝ) y).prodMk (hasFDerivAt_id y))
    simpa only [K,L,ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,map_one,
      zero_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.inr_apply,Function.comp_def] using hcomp.hasDerivAt
  have hsingle : DifferentiableAt ℝ (fun z => F p.1 z) y :=
    ((hF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)).differentiableAt
  have he : (L.comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ)) 1=deriv (F p.1) y := by
    have hd := hsingle.hasDerivAt.sub_const p.2
    exact hpart.unique hd
  have hinv : (L.comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ)).IsInvertible := by
    refine ⟨(ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (deriv (F p.1) y) (hn p.1 y))),?_⟩
    apply ContinuousLinearMap.ext
    intro z
    change z*deriv (F p.1) y = _
    rw [show z=z • (1:ℝ) by simp, map_smul,smul_eq_mul,he]
    simp only [smul_eq_mul,mul_one]
  have hloc := hK.contDiffAt.contDiffAt_implicitFunction (by simp) hinv
  apply hloc.congr_of_eventuallyEq
  filter_upwards [hK.contDiffAt.eventually_apply_implicitFunction (by simp) hinv] with q hq
  apply (F q.1).injective
  rw [(F q.1).apply_symm_apply]
  dsimp only [K] at hq
  have hp : F p.1 y=p.2 := (F p.1).apply_symm_apply p.2
  rw [hp,sub_self] at hq
  exact (sub_eq_zero.mp hq).symm
end StronglyRationalVOA.PositiveCircleGeometry

open Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.PositiveCircleGeometry
 
structure SmoothLift where
  toFun : ℝ → ℝ
  add_one : ∀ x, toFun (x+1)=toFun x+1
  smooth : ContDiff ℝ ∞ toFun
  derivative_pos : ∀ x, 0 < deriv toFun x
instance : CoeFun SmoothLift (fun _ => ℝ → ℝ) := ⟨SmoothLift.toFun⟩
namespace SmoothLift
variable (φ : SmoothLift)
lemma strictMono : StrictMono φ := strictMono_of_deriv_pos φ.derivative_pos

def degreeOne : CircleDeg1Lift where
  toFun := φ
  monotone' := φ.strictMono.monotone
  map_add_one' := φ.add_one
lemma surjective : Function.Surjective φ := φ.degreeOne.continuous_iff_surjective.mp φ.smooth.continuous

def orderIso : ℝ ≃o ℝ := StrictMono.orderIsoOfRightInverse φ φ.strictMono
  (Function.surjInv φ.surjective) (Function.rightInverse_surjInv φ.surjective)
@[simp] lemma orderIso_apply (x : ℝ) : φ.orderIso x=φ x := rfl

 

def interpolate (t x : ℝ) : ℝ := (1-Real.smoothTransition t)*x+Real.smoothTransition t*φ x
lemma interpolate_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ.interpolate p.1 p.2) := by
  exact ((contDiff_const.sub (Real.smoothTransition.contDiff.comp contDiff_fst)).mul contDiff_snd).add
    ((Real.smoothTransition.contDiff.comp contDiff_fst).mul (φ.smooth.comp contDiff_snd))
lemma interpolate_zero (x : ℝ) : φ.interpolate 0 x=x := by simp [interpolate]
lemma interpolate_one (x : ℝ) : φ.interpolate 1 x=φ x := by simp [interpolate]
lemma interpolate_add_one (t x : ℝ) : φ.interpolate t (x+1)=φ.interpolate t x+1 := by
  simp only [interpolate,φ.add_one]; ring
lemma interpolate_derivative (t x : ℝ) :
    HasDerivAt (φ.interpolate t) (1-Real.smoothTransition t+Real.smoothTransition t*deriv φ x) x := by
  unfold interpolate
  convert ((hasDerivAt_id x).const_mul (1-Real.smoothTransition t)).add
    (((φ.smooth.differentiable (by simp) x).hasDerivAt).const_mul (Real.smoothTransition t)) using 1 <;> first | rfl | simp only [mul_one]
lemma interpolate_derivative_pos (t x : ℝ) :
    0 < 1-Real.smoothTransition t+Real.smoothTransition t*deriv φ x := by
  have h0 := Real.smoothTransition.nonneg t
  have h1 := Real.smoothTransition.le_one t
  by_cases h : Real.smoothTransition t=0
  · simp [h]
  · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr h1)
      (mul_pos (lt_of_le_of_ne h0 (Ne.symm h)) (φ.derivative_pos x))
def isotopy (t : ℝ) : SmoothLift where
  toFun := φ.interpolate t
  add_one := φ.interpolate_add_one t
  smooth := φ.interpolate_smooth.comp (contDiff_const.prodMk contDiff_id)
  derivative_pos := fun x => by rw [(φ.interpolate_derivative t x).deriv]; exact φ.interpolate_derivative_pos t x
@[simp] lemma isotopy_apply (t x : ℝ) : φ.isotopy t x=φ.interpolate t x := rfl
end SmoothLift
end StronglyRationalVOA.PositiveCircleGeometry

open Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.PositiveCircleGeometry.SmoothLift
variable (φ : SmoothLift)
def inverse (t x : ℝ) : ℝ := (φ.isotopy t).orderIso.symm x
lemma inverse_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ.inverse p.1 p.2) := by
  apply parameter_inverse_smooth (fun t => (φ.isotopy t).orderIso)
  · exact φ.interpolate_smooth
  · intro t x
    exact ne_of_gt ((φ.isotopy t).derivative_pos x)
@[simp] lemma interpolate_inverse (t x : ℝ) : φ.interpolate t (φ.inverse t x)=x :=
  (φ.isotopy t).orderIso.apply_symm_apply x
@[simp] lemma inverse_interpolate (t x : ℝ) : φ.inverse t (φ.interpolate t x)=x :=
  (φ.isotopy t).orderIso.symm_apply_apply x
lemma inverse_add_one (t x : ℝ) : φ.inverse t (x+1)=φ.inverse t x+1 := by
  apply (φ.isotopy t).strictMono.injective
  change φ.interpolate t (φ.inverse t (x+1))=φ.interpolate t (φ.inverse t x+1)
  rw [φ.interpolate_inverse,φ.interpolate_add_one,φ.interpolate_inverse]
def jacobian (t y : ℝ) : ℝ := 1-Real.smoothTransition t+Real.smoothTransition t*deriv φ y
lemma jacobian_pos (t y : ℝ) : 0 < φ.jacobian t y := φ.interpolate_derivative_pos t y
lemma jacobian_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ.jacobian p.1 p.2) := by
  exact (contDiff_const.sub (Real.smoothTransition.contDiff.comp contDiff_fst)).add
    ((Real.smoothTransition.contDiff.comp contDiff_fst).mul ((contDiff_infty_iff_deriv.mp φ.smooth).2.comp contDiff_snd))
def velocity (t x : ℝ) : ℝ := deriv Real.smoothTransition t*(φ (φ.inverse t x)-φ.inverse t x)
lemma velocity_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ.velocity p.1 p.2) := by
  exact ((contDiff_infty_iff_deriv.mp (Real.smoothTransition.contDiff (n := ⊤))).2.comp contDiff_fst).mul
    ((φ.smooth.comp φ.inverse_smooth).sub φ.inverse_smooth)
lemma inverse_space_derivative (t x : ℝ) :
    HasDerivAt (φ.inverse t) (φ.jacobian t (φ.inverse t x))⁻¹ x := by
  apply HasDerivAt.of_local_left_inverse
    (((φ.inverse_smooth.comp (contDiff_const.prodMk contDiff_id)).continuous).continuousAt)
    (φ.interpolate_derivative t (φ.inverse t x))
    (ne_of_gt (φ.jacobian_pos t (φ.inverse t x)))
  exact Filter.Eventually.of_forall (φ.interpolate_inverse t)
lemma inverse_time_derivative (t x : ℝ) :
    HasDerivAt (fun s => φ.inverse s x) (-φ.velocity t x/(φ.jacobian t (φ.inverse t x))) t := by
  have hd := ((φ.inverse_smooth.comp (contDiff_id.prodMk (contDiff_const (c := x)))).differentiable (by simp) t).hasDerivAt
  have hr := ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp) t).hasDerivAt
  have hp := (φ.smooth.differentiable (by simp) (φ.inverse t x)).hasDerivAt.comp t hd
  have he := ((hasDerivAt_const t (1:ℝ)).sub hr).mul hd |>.add (hr.mul hp)
  have he0 := he.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun s => (φ.interpolate_inverse s x).symm))
  have hz := he0.unique (hasDerivAt_const t x)
  have hval : deriv (fun s => φ.inverse s x) t= -φ.velocity t x/φ.jacobian t (φ.inverse t x) := by
    apply (eq_div_iff (ne_of_gt (φ.jacobian_pos t (φ.inverse t x)))).mpr
    dsimp only [velocity,jacobian]
    simp only [Function.comp_def,id_eq,Pi.sub_apply] at hz
    linear_combination hz
  exact hval ▸ hd
lemma velocity_space_derivative (t x : ℝ) :
    HasDerivAt (φ.velocity t)
      (deriv Real.smoothTransition t*(deriv φ (φ.inverse t x)-1)/(φ.jacobian t (φ.inverse t x))) x := by
  have he := (((φ.smooth.differentiable (by simp) (φ.inverse t x)).hasDerivAt.comp x
    (φ.inverse_space_derivative t x)).sub (φ.inverse_space_derivative t x)).const_mul (deriv Real.smoothTransition t)
  unfold velocity
  convert he using 1 <;> first | rfl | ring
lemma jacobian_space_derivative (t y : ℝ) : HasDerivAt (φ.jacobian t)
    (Real.smoothTransition t*deriv (deriv φ) y) y := by
  have he := ((contDiff_infty_iff_deriv.mp φ.smooth).2.differentiable (by simp) y).hasDerivAt.const_mul (Real.smoothTransition t)
  convert he.const_add (1-Real.smoothTransition t) using 1
  rfl
lemma jacobian_time_derivative (t y : ℝ) : HasDerivAt (fun s => φ.jacobian s y)
    (deriv Real.smoothTransition t*(deriv φ y-1)) t := by
  have hr := ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp) t).hasDerivAt
  unfold jacobian
  convert ((hasDerivAt_const t (1:ℝ)).sub hr).add (hr.mul_const (deriv φ y)) using 1
  first | rfl | ring

 
def density (g : ℝ → ℝ) (k : ℕ) (t x : ℝ) : ℝ :=
  φ.jacobian t (φ.inverse t x)^k*g (φ.inverse t x)
lemma density_smooth {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (k : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ.density g k p.1 p.2) := by
  exact ((φ.jacobian_smooth.comp (contDiff_fst.prodMk φ.inverse_smooth)).pow k).mul
    (hg.comp φ.inverse_smooth)
lemma density_space_derivative {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (k : ℕ) (t x : ℝ) :
    HasDerivAt (φ.density g k t)
    ((k:ℝ)*φ.jacobian t (φ.inverse t x)^(k-1)*
      (Real.smoothTransition t*deriv (deriv φ) (φ.inverse t x)/(φ.jacobian t (φ.inverse t x)))*g (φ.inverse t x)+
      φ.jacobian t (φ.inverse t x)^k*(deriv g (φ.inverse t x)/(φ.jacobian t (φ.inverse t x)))) x := by
  have hi := φ.inverse_space_derivative t x
  have hj := (φ.jacobian_space_derivative t (φ.inverse t x)).comp x hi
  have hd := (hj.pow k).mul ((hg.differentiable (by simp) (φ.inverse t x)).hasDerivAt.comp x hi)
  unfold density
  convert hd using 1 <;> rfl
lemma density_time_derivative {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (k : ℕ) (t x : ℝ) :
    HasDerivAt (fun s => φ.density g k s x)
      ((k:ℝ)*deriv (φ.velocity t) x*φ.density g k t x-φ.velocity t x*deriv (φ.density g k t) x) t := by
  have hi := φ.inverse_time_derivative t x
  have hr := ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp) t).hasDerivAt
  have hp := (((contDiff_infty_iff_deriv.mp φ.smooth).2.differentiable (by simp)
    (φ.inverse t x)).hasDerivAt).comp t hi
  have hj := ((hasDerivAt_const t (1:ℝ)).sub hr).add (hr.mul hp)
  have hd := (hj.pow k).mul ((hg.differentiable (by simp) (φ.inverse t x)).hasDerivAt.comp t hi)
  rw [(φ.velocity_space_derivative t x).deriv,(φ.density_space_derivative hg k t x).deriv]
  unfold density jacobian
  convert hd using 1 <;> first | rfl | skip
  have hn := ne_of_gt (φ.jacobian_pos t (φ.inverse t x))
  dsimp only [jacobian] at hn
  simp only [jacobian,Function.comp_def,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply]
  generalize hJ : 1-Real.smoothTransition t+Real.smoothTransition t*deriv φ (φ.inverse t x)=J at *
  cases k with
  | zero => simp; ring
  | succ k =>
    simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,pow_succ]
    field_simp [hn]
    ring
lemma derivative_periodic : Function.Periodic (deriv φ) 1 := by
  intro x
  have h : (fun y => φ (y+1))=(fun y => φ y+1) := funext φ.add_one
  have he := congrFun (congrArg deriv h) x
  simpa only [deriv_comp_add_const,deriv_add_const] using he
lemma velocity_periodic (t : ℝ) : Function.Periodic (φ.velocity t) 1 := by
  intro x
  simp only [velocity,φ.inverse_add_one,φ.add_one]
  ring
lemma density_periodic {g : ℝ → ℝ} (hg : Function.Periodic g 1) (k : ℕ) (t : ℝ) :
    Function.Periodic (φ.density g k t) 1 := by
  intro x
  simp only [density,φ.inverse_add_one,jacobian,φ.derivative_periodic (φ.inverse t x),hg (φ.inverse t x)]
lemma inverse_zero (x : ℝ) : φ.inverse 0 x=x := by
  have h := φ.interpolate_inverse 0 x
  rwa [φ.interpolate_zero] at h
lemma density_zero (g : ℝ → ℝ) (k : ℕ) (x : ℝ) : φ.density g k 0 x=g x := by
  simp [density,jacobian,φ.inverse_zero]
lemma velocity_stationary {t : ℝ} (ht : t ∉ Set.Icc 0 1) : φ.velocity t=0 := by
  have he : deriv Real.smoothTransition t=0 := by
    rcases lt_or_ge t 0 with h | h
    · have hh : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
        filter_upwards [Iio_mem_nhds h] with s hs
        exact Real.smoothTransition.zero_of_nonpos hs.le
      rw [hh.deriv_eq,deriv_const]
    · have h1 : 1 < t := lt_of_not_ge (fun h1 => ht ⟨h,h1⟩)
      have hh : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1:ℝ) := by
        filter_upwards [Ioi_mem_nhds h1] with s hs
        exact Real.smoothTransition.one_of_one_le hs.le
      rw [hh.deriv_eq,deriv_const]
  funext x
  simp only [velocity,he,zero_mul,Pi.zero_apply]
end StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

open Filter MeasureTheory Set
open scoped Topology ContDiff
namespace StronglyRationalVOA
lemma joint_space_deriv_smooth {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (fun x => f (p.1,x)) p.2) := by
  have he (p : ℝ × ℝ) : deriv (fun x => f (p.1,x)) p.2 = fderiv ℝ f p (0,1) := by
    have hg : HasFDerivAt (fun x : ℝ => (p.1,x)) (ContinuousLinearMap.inr ℝ ℝ ℝ) p.2 := by
      convert (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) p.2) using 1 <;> rfl
    have h := (hf.differentiable (by simp) p).hasFDerivAt.comp p.2 hg
    convert h.hasDerivAt.deriv using 1 <;> rfl
  simp_rw [he]
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
lemma joint_iterated_space_deriv_smooth {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv k (fun x => f (p.1,x)) p.2) := by
  induction k with
  | zero => exact hf
  | succ k ih => simpa only [iteratedDeriv_succ] using joint_space_deriv_smooth ih

lemma summable_circle_decay : Summable (fun n : ℤ => ((1+|(n:ℝ)|)^2)⁻¹) := by
  apply summable_int_iff_summable_nat_and_neg.mpr
  have h : Summable (fun n : ℕ => ((1+(n:ℝ))^2)⁻¹) := by
    simpa only [Nat.cast_add,Nat.cast_one,add_comm] using
      (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2))
  constructor
  · simpa only [Int.cast_natCast,Nat.abs_cast] using h
  · simpa only [Int.cast_neg,Int.cast_natCast,abs_neg,Nat.abs_cast] using h

namespace SmoothCircleFunction
lemma coefficient_weighted_bound (f : SmoothCircleFunction) (k : ℕ) {M : ℝ}
    (hM : 0 ≤ M) (h0 : ∀ x ∈ Icc 0 (2*Real.pi), ‖f x‖ ≤ M)
    (hk : ∀ x ∈ Icc 0 (2*Real.pi), ‖iteratedDeriv k f x‖ ≤ M) (n : ℤ) :
    ‖f.coefficient n‖*(1+|(n:ℝ)|)^k ≤ 2^k*M := by
  by_cases hn : n=0
  · subst n
    simp only [Int.cast_zero,abs_zero,add_zero,one_pow,mul_one]
    exact (coefficient_norm_le h0 0).trans (le_mul_of_one_le_left hM (one_le_pow₀ (by norm_num)))
  · have hx : 1 ≤ |(n:ℝ)| := by exact_mod_cast Int.one_le_abs hn
    have he := congrArg norm (f.coefficient_iteratedDeriv k hn)
    have hn' : ‖(n:ℂ)‖=|(n:ℝ)| := by rw [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
    simp only [norm_mul,norm_pow,Complex.norm_I,one_mul,hn'] at he
    have hb : |(n:ℝ)|^k*‖f.coefficient n‖ ≤ M := he.trans_le (coefficient_norm_le hk n)
    calc
      _ ≤ ‖f.coefficient n‖*(2*|(n:ℝ)|)^k := by gcongr; linarith
      _ = 2^k*(|(n:ℝ)|^k*‖f.coefficient n‖) := by rw [mul_pow]; ring
      _ ≤ 2^k*M := mul_le_mul_of_nonneg_left hb (by positivity)
end SmoothCircleFunction
end StronglyRationalVOA

end

end OAI
