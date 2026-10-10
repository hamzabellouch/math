import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.ObservableScalars

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
open Set MeasureTheory
open Set
open MeasureTheory Filter
open Set MeasureTheory Filter UniformSpace
open Set UniformSpace
open Set UniformSpace Filter
open Set MeasureTheory Filter
open UniformSpace Set Filter
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma rotation_conjugate_commutant (hc : A.toVertexAlgebra.C2Cofinite)
    (I : ProperCircleArc) (t : ℝ) {Q : Completion V →L[ℂ] Completion V}
    (hQ : Q ∈ (U.intervalAlgebra hc (I.translate t)).commutant) :
    U.rotation (-t)*Q*U.rotation t ∈ (U.intervalAlgebra hc I).commutant := by
  rw [← SetLike.mem_coe,intervalAlgebra,localAlgebra,LocalOperatorAlgebra.coe_generated_commutant]
  have hdata : ∀ B ∈ U.localGraphData hc I.carrier,
      (U.rotation (-t)*Q*U.rotation t)*B=B*(U.rotation (-t)*Q*U.rotation t) := by
    rintro B ⟨a,d,ha,f,hf,i,j,rfl⟩
    apply ClosedGraphData.entry_commutes_of_graph_invariant
    · intro x y hxy
      exact U.rotation_conjugate_graph hc ha f I hf t hQ hxy
    · intro x y hxy
      have H := U.rotation_conjugate_graph hc ha f I hf t (star_mem hQ) hxy
      have he : (U.rotation (-t)*Q*U.rotation t).adjoint=
          U.rotation (-t)*Q.adjoint*U.rotation t := by
        change star (U.rotation (-t)*Q*U.rotation t)=_
        rw [star_mul,star_mul]
        simp only [ContinuousLinearMap.star_eq_adjoint,U.rotation_adjoint,neg_neg,mul_assoc]
      rw [he]
      exact H
  intro B hB
  rcases hB with hB | hB
  · exact (hdata B hB).symm
  · apply (hdata B ?_).symm
    obtain ⟨a,d,ha,f,hf,i,j,he⟩ := hB
    refine ⟨a,d,ha,f,hf,j,i,?_⟩
    have H := congrArg star he
    rwa [star_star,ClosedGraphData.star_entry] at H
 
lemma intervalAlgebra_rotation_mem (hc : A.toVertexAlgebra.C2Cofinite)
    (I : ProperCircleArc) (t : ℝ) {B : Completion V →L[ℂ] Completion V}
    (hB : B ∈ U.intervalAlgebra hc I) :
    U.rotation t*B*U.rotation (-t) ∈ U.intervalAlgebra hc (I.translate t) := by
  rw [← VonNeumannAlgebra.commutant_commutant (U.intervalAlgebra hc (I.translate t)),
    VonNeumannAlgebra.mem_commutant_iff]
  intro Q hQ
  have h := (VonNeumannAlgebra.mem_commutant_iff.mp
    (U.rotation_conjugate_commutant hc I t hQ)) B hB
  have h1 : U.rotation t*U.rotation (-t)=1 := by rw [← U.rotation_add,add_neg_cancel,U.rotation_zero]
  have he : (U.rotation t*B*U.rotation (-t))*Q=Q*(U.rotation t*B*U.rotation (-t)) := by
    calc
      _ = U.rotation t*(B*(U.rotation (-t)*Q*U.rotation t))*U.rotation (-t) := by
        simp only [mul_assoc,h1,mul_one]
      _ = U.rotation t*((U.rotation (-t)*Q*U.rotation t)*B)*U.rotation (-t) := by rw [h]
      _ = _ := by
        simp only [mul_assoc]
        rw [← mul_assoc (U.rotation t) (U.rotation (-t)),h1,one_mul]
  exact he.symm
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma rotation_fixed_scalar {x : Completion V} (hx : ∀ t : ℝ, U.rotation t x=x) :
    ∃ c : ℂ, x=c • (A.vacuum : Completion V) := by
  let : ∀ d, FiniteDimensional ℂ (A.grade d) := A.grade_finite
  apply U.hamiltonian_kernel
  rw [conformalHamiltonian,U.energyOperator_graph_iff]
  intro d
  by_cases hd : d=0
  · subst d
    simp
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have H := congrArg (fun y => U.energyCoordinates y d) (hx (Real.pi/d))
  rw [U.rotation_coordinates,HilbertScale.rotation_apply,div_mul_cancel₀ _ hd',Complex.exp_pi_mul_I] at H
  have hz : U.energyCoordinates x d=0 := by
    have H' : (-2 : ℂ) • U.energyCoordinates x d=0 := by
      rw [show (-2:ℂ)=(-1)-1 by norm_num,sub_smul,one_smul,H,sub_self]
    exact (smul_eq_zero.mp H').resolve_left (by norm_num)
  simp [hz]
 
lemma interval_invariant_subspace (hc : A.toVertexAlgebra.C2Cofinite)
    (S : Submodule ℂ (Completion V)) (hclosed : IsClosed (S : Set (Completion V)))
    (hS : ∀ I : ProperCircleArc, ∀ B ∈ U.intervalAlgebra hc I, ∀ x ∈ S, B x ∈ S) :
    S=⊥ ∨ S=⊤ := by
  let : IsClosed (S : Set (Completion V)) := hclosed
  have hcomm : ∀ I : ProperCircleArc, S.starProjection ∈ (U.intervalAlgebra hc I).commutant := by
    intro I
    rw [VonNeumannAlgebra.mem_commutant_iff]
    intro B hB
    exact ClosedGraphData.commutes_projection_of_reduces S B (hS I B hB)
      (hS I B.adjoint (star_mem hB))
  obtain ⟨c,he⟩ := U.interval_commutant_scalar hc hcomm
  by_cases hbot : S=⊥
  · exact Or.inl hbot
  right
  have hex : ∃ x ∈ S, x ≠ 0 := by
    by_contra! h
    apply hbot
    exact le_antisymm (fun x hx => (Submodule.mem_bot _).mpr (h x hx)) bot_le
  obtain ⟨x,hx,hxn⟩ := hex
  have hcx : c • x=x := by
    have H := S.starProjection_eq_self_iff.mpr hx
    rwa [he,smul_apply,one_apply_eq_self] at H
  have hc1 : c=1 := smul_left_injective ℂ hxn (hcx.trans (one_smul ℂ x).symm)
  apply top_unique
  intro y _
  have hy := S.starProjection_apply_mem y
  simpa only [he,hc1,one_smul,one_apply_eq_self] using hy
lemma conformalHamiltonian_nonnegative {x y : Completion V}
    (hxy : (x,y) ∈ U.conformalHamiltonian.graph) : 0 ≤ (inner ℂ x y).re := by
  let : ∀ d, FiniteDimensional ℂ (A.grade d) := A.grade_finite
  have H := (U.energyOperator_graph_iff (fun d => d) x y).mp hxy
  rw [← U.energyCoordinates.inner_map_map x y,
    ← (lp.hasSum_inner (U.energyCoordinates x) (U.energyCoordinates y)).tsum_eq,
    Complex.re_tsum (lp.hasSum_inner (U.energyCoordinates x) (U.energyCoordinates y)).summable]
  apply tsum_nonneg
  intro d
  rw [H d,inner_smul_right,Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact mul_nonneg (Nat.cast_nonneg d) (inner_self_nonneg (𝕜 := ℂ))
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set
namespace StronglyRationalVOA.ProperCircleArc
lemma translate_add (I : ProperCircleArc) (s t : ℝ) : (I.translate s).translate t=I.translate (s+t) := by
  cases I
  simp only [translate]
  congr 1 <;> ring
lemma translate_zero (I : ProperCircleArc) : I.translate 0=I := by
  cases I
  simp [translate]
end StronglyRationalVOA.ProperCircleArc
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma intervalAlgebra_rotation_mem_iff (hc : A.toVertexAlgebra.C2Cofinite)
    (I : ProperCircleArc) (t : ℝ) (B : Completion V →L[ℂ] Completion V) :
    U.rotation t*B*U.rotation (-t) ∈ U.intervalAlgebra hc (I.translate t) ↔ B ∈ U.intervalAlgebra hc I := by
  constructor
  · intro h
    have H := U.intervalAlgebra_rotation_mem hc (I.translate t) (-t) h
    rw [ProperCircleArc.translate_add,add_neg_cancel,ProperCircleArc.translate_zero,neg_neg] at H
    have hi : U.rotation (-t)*U.rotation t=1 := by rw [← U.rotation_add,neg_add_cancel,U.rotation_zero]
    have he : U.rotation (-t)*(U.rotation t*B*U.rotation (-t))*U.rotation t=B := by
      simp only [mul_assoc,hi,mul_one]
      rw [← mul_assoc,hi,one_mul]
    rwa [he] at H
  · exact U.intervalAlgebra_rotation_mem hc I t
lemma rotation_two_pi : U.rotation (2*Real.pi)=1 := by
  let : ∀ d, FiniteDimensional ℂ (A.grade d) := A.grade_finite
  apply ContinuousLinearMap.ext
  intro x
  apply U.energyCoordinates.injective
  ext d
  rw [U.rotation_coordinates,HilbertScale.rotation_apply]
  have he : Complex.exp (((2*Real.pi)*(d:ℝ) : ℝ)*Complex.I)=1 := by
    calc
      _ = Complex.exp ((d:ℂ)*(2*Real.pi*Complex.I)) := by congr 1; push_cast; ring
      _ = Complex.exp (2*Real.pi*Complex.I)^d := Complex.exp_nat_mul _ d
      _ = 1 := by rw [Complex.exp_two_pi_mul_I,one_pow]
  rw [he,one_smul]
  rfl
lemma rotation_periodic : Function.Periodic U.rotation (2*Real.pi) := by
  intro t
  rw [U.rotation_add,U.rotation_two_pi,mul_one]
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open scoped ContDiff
namespace StronglyRationalVOA
 

structure SmoothCircleLift where
  toOrderIso : ℝ ≃o ℝ
  smooth : ContDiff ℝ ∞ toOrderIso
  inverse_smooth : ContDiff ℝ ∞ toOrderIso.symm
  period : ∀ t, toOrderIso (t+2*Real.pi)=toOrderIso t+2*Real.pi
namespace SmoothCircleLift
instance : CoeFun SmoothCircleLift (fun _ => ℝ → ℝ) := ⟨fun F => F.toOrderIso⟩
@[ext] lemma ext {F G : SmoothCircleLift} (h : ∀ t, F t=G t) : F=G := by
  cases F with
  | mk f hf hfi hp =>
    cases G with
    | mk g hg hgi hgp =>
      have he : f=g := DFunLike.ext _ _ h
      subst g
      rfl
def identity : SmoothCircleLift where
  toOrderIso := OrderIso.refl ℝ
  smooth := contDiff_id
  inverse_smooth := contDiff_id
  period := fun _ => rfl
def compose (F G : SmoothCircleLift) : SmoothCircleLift where
  toOrderIso := G.toOrderIso.trans F.toOrderIso
  smooth := F.smooth.comp G.smooth
  inverse_smooth := G.inverse_smooth.comp F.inverse_smooth
  period := by intro t; change F (G (t+2*Real.pi))=F (G t)+2*Real.pi; rw [G.period,F.period]
def inverse (F : SmoothCircleLift) : SmoothCircleLift where
  toOrderIso := F.toOrderIso.symm
  smooth := F.inverse_smooth
  inverse_smooth := F.smooth
  period := by
    intro t
    apply F.toOrderIso.injective
    rw [F.toOrderIso.apply_symm_apply,F.period,F.toOrderIso.apply_symm_apply]
instance : Group SmoothCircleLift where
  mul := compose
  one := identity
  inv := inverse
  mul_assoc F G H := by ext; rfl
  one_mul F := by ext; rfl
  mul_one F := by ext; rfl
  inv_mul_cancel F := by ext t; exact F.toOrderIso.symm_apply_apply t
@[simp] lemma one_apply (t : ℝ) : (1 : SmoothCircleLift) t=t := rfl
@[simp] lemma mul_apply (F G : SmoothCircleLift) (t : ℝ) : (F*G) t=F (G t) := rfl
@[simp] lemma inv_apply_apply (F : SmoothCircleLift) (t : ℝ) : F⁻¹ (F t)=t := F.toOrderIso.symm_apply_apply t
@[simp] lemma apply_inv_apply (F : SmoothCircleLift) (t : ℝ) : F (F⁻¹ t)=t := F.toOrderIso.apply_symm_apply t
 
def rotation (s : ℝ) : SmoothCircleLift where
  toOrderIso := OrderIso.addRight s
  smooth := contDiff_id.add contDiff_const
  inverse_smooth := by
    change ContDiff ℝ ∞ (fun x : ℝ => x + -s)
    exact contDiff_id.add contDiff_const
  period := by intro t; change t+2*Real.pi+s=t+s+2*Real.pi; ring
@[simp] lemma rotation_apply (s t : ℝ) : rotation s t=t+s := rfl
lemma rotation_zero : rotation 0=1 := by ext; simp
lemma rotation_add (s t : ℝ) : rotation (s+t)=rotation s*rotation t := by ext; simp; ring
lemma circle_periodic (F : SmoothCircleLift) : Function.Periodic (fun t : ℝ => (F t : AddCircle (2*Real.pi))) (2*Real.pi) := by
  intro t
  change ((F.toOrderIso (t+2*Real.pi) : ℝ) : AddCircle (2*Real.pi)) =
    (F.toOrderIso t : AddCircle (2*Real.pi))
  rw [F.period,AddCircle.coe_add]
  simp
 
def onCircle (F : SmoothCircleLift) : AddCircle (2*Real.pi) → AddCircle (2*Real.pi) := F.circle_periodic.lift
@[simp] lemma onCircle_coe (F : SmoothCircleLift) (t : ℝ) : F.onCircle (t : AddCircle (2*Real.pi))=(F t : AddCircle (2*Real.pi)) := rfl
lemma onCircle_mul (F G : SmoothCircleLift) (t : AddCircle (2*Real.pi)) :
    (F*G).onCircle t=F.onCircle (G.onCircle t) := by
  induction t using QuotientAddGroup.induction_on with
  | H t => rfl
lemma onCircle_one (t : AddCircle (2*Real.pi)) : (1 : SmoothCircleLift).onCircle t=t := by
  induction t using QuotientAddGroup.induction_on with
  | H t => rfl
lemma onCircle_inverse (F : SmoothCircleLift) (t : AddCircle (2*Real.pi)) : F⁻¹.onCircle (F.onCircle t)=t := by
  rw [← onCircle_mul,inv_mul_cancel,onCircle_one]
lemma differentiable (F : SmoothCircleLift) : Differentiable ℝ F :=
  F.smooth.differentiable (by simp)
lemma derivative_positive (F : SmoothCircleLift) (t : ℝ) : 0 < deriv F t := by
  have hn : 0 ≤ deriv F t := F.toOrderIso.monotone.deriv_nonneg
  have hF := (F.differentiable t).hasDerivAt
  have hI := ((F⁻¹).differentiable (F t)).hasDerivAt
  have hh : HasDerivAt (fun x : ℝ => x) (deriv (fun x => (F⁻¹ : SmoothCircleLift) x) (F t)*deriv F t) t := by
    simpa only [Function.comp_def,inv_apply_apply] using hI.comp t hF
  have he : deriv (fun x => (F⁻¹ : SmoothCircleLift) x) (F t)*deriv F t=1 := hh.unique (hasDerivAt_id t)
  exact lt_of_le_of_ne hn (by intro hz; rw [← hz,mul_zero] at he; norm_num at he)
lemma continuous_onCircle (F : SmoothCircleLift) : Continuous F.onCircle := by
  exact ((AddCircle.continuous_mk' (2*Real.pi)).comp F.smooth.continuous).quotient_liftOn' _
 
def circleHomeomorph (F : SmoothCircleLift) :
    AddCircle (2*Real.pi) ≃ₜ AddCircle (2*Real.pi) where
  toFun := F.onCircle
  invFun := F⁻¹.onCircle
  left_inv := F.onCircle_inverse
  right_inv := by intro t; simpa using F⁻¹.onCircle_inverse t
  continuous_toFun := F.continuous_onCircle
  continuous_invFun := F⁻¹.continuous_onCircle
lemma shift_periodic (F : SmoothCircleLift) : Function.Periodic (fun t => F t-t) (2*Real.pi) := by
  intro t
  change F (t+2*Real.pi)-(t+2*Real.pi)=F t-t
  rw [F.period]
  ring
lemma integer_shift (F : SmoothCircleLift) (n : ℤ) (t : ℝ) :
    F (t+n*(2*Real.pi))=F t+n*(2*Real.pi) := by
  have h := F.shift_periodic.zsmul n t
  simp only [zsmul_eq_mul] at h
  linarith
lemma deck_central (F : SmoothCircleLift) (n : ℤ) :
    rotation (n*(2*Real.pi))*F=F*rotation (n*(2*Real.pi)) := by
  ext t
  simp only [mul_apply,rotation_apply,F.integer_shift]
lemma deck_onCircle (n : ℤ) (t : AddCircle (2*Real.pi)) :
    (rotation (n*(2*Real.pi))).onCircle t=t := by
  induction t using QuotientAddGroup.induction_on with
  | H t =>
    rw [onCircle_coe,rotation_apply,AddCircle.coe_add]
    have h : ((n*(2*Real.pi) : ℝ) : AddCircle (2*Real.pi))=0 := by
      exact (AddCircle.coe_eq_zero_iff (2*Real.pi)).mpr ⟨n,by simp [zsmul_eq_mul]⟩
    rw [h,add_zero]
 

lemma onCircle_eq_iff (F G : SmoothCircleLift) : F.onCircle=G.onCircle ↔
    ∃ n : ℤ, F=rotation (n*(2*Real.pi))*G := by
  constructor
  · intro h
    have hz (x : ℝ) : F x-G x ∈ AddSubgroup.zmultiples (2*Real.pi) := by
      have hq : ((F x-G x:ℝ) : AddCircle (2*Real.pi))=0 := by
        rw [AddCircle.coe_sub]
        exact sub_eq_zero.mpr (congrFun h (x:AddCircle (2*Real.pi)))
      exact (QuotientAddGroup.eq_zero_iff (F x-G x)).mp hq
    let D : ℝ → AddSubgroup.zmultiples (2*Real.pi) := fun x => ⟨F x-G x,hz x⟩
    have hD : Continuous D := (F.smooth.continuous.sub G.smooth.continuous).subtype_mk hz
    have hl : IsLocallyConstant D := (IsLocallyConstant.iff_continuous D).mpr hD
    have he (x : ℝ) : F x-G x=F 0-G 0 := congrArg Subtype.val
      (hl.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ x) (Set.mem_univ 0))
    obtain ⟨n,hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (hz 0)
    refine ⟨n,?_⟩
    ext x
    simp only [mul_apply,rotation_apply]
    simp only [zsmul_eq_mul] at hn
    linarith [he x]
  · rintro ⟨n,rfl⟩
    funext x
    rw [onCircle_mul,deck_onCircle]
 
def circleAction : SmoothCircleLift →* Equiv.Perm (AddCircle (2*Real.pi)) where
  toFun F := F.circleHomeomorph.toEquiv
  map_one' := by ext x; exact onCircle_one x
  map_mul' F G := by ext x; exact onCircle_mul F G x
lemma circleAction_kernel (F : SmoothCircleLift) : F ∈ circleAction.ker ↔
    ∃ n : ℤ, F=rotation (n*(2*Real.pi)) := by
  change circleAction F=1 ↔ _
  have he : circleAction F=1 ↔ F.onCircle=(1 : SmoothCircleLift).onCircle := by
    constructor
    · intro h
      funext x
      rw [onCircle_one]
      exact congrArg (fun e : Equiv.Perm (AddCircle (2*Real.pi)) => e x) h
    · intro h
      ext x
      change F.onCircle x=x
      simpa only [onCircle_one] using congrFun h x
  rw [he,onCircle_eq_iff]
  simp only [mul_one]
end SmoothCircleLift
 

def SmoothCircleDiffeomorphism := SmoothCircleLift ⧸ SmoothCircleLift.circleAction.ker
instance : Group SmoothCircleDiffeomorphism := inferInstanceAs
  (Group (SmoothCircleLift ⧸ SmoothCircleLift.circleAction.ker))
end StronglyRationalVOA

open UniformSpace
open scoped ContDiff
namespace StronglyRationalVOA.SmoothCircleLift
variable (F : SmoothCircleLift)
def unitParameter (x : ℝ) : ℝ := F (2*Real.pi*x)/(2*Real.pi)
lemma unitParameter_smooth : ContDiff ℝ ∞ F.unitParameter :=
  (F.smooth.comp (contDiff_const.mul contDiff_id)).div_const _
lemma unitParameter_derivative (x : ℝ) :
    HasDerivAt F.unitParameter (deriv F (2*Real.pi*x)) x := by
  have h := (((F.differentiable (2*Real.pi*x)).hasDerivAt).comp x
    ((hasDerivAt_id x).const_mul (2*Real.pi))).div_const (2*Real.pi)
  convert h using 1 <;> first | rfl | field_simp [Real.pi_ne_zero]
def unitLift : PositiveCircleGeometry.SmoothLift where
  toFun := F.unitParameter
  add_one := by
    intro x
    dsimp only [unitParameter]
    rw [mul_add,mul_one,F.period,add_div,div_self (by positivity : (2*Real.pi:ℝ) ≠ 0)]
  smooth := F.unitParameter_smooth
  derivative_pos := fun x => by rw [(F.unitParameter_derivative x).deriv]; exact F.derivative_positive _
@[simp] lemma unitLift_apply (x : ℝ) : F.unitLift x=F (2*Real.pi*x)/(2*Real.pi) := rfl
lemma unitLift_inverse_one (x : ℝ) :
    F.unitLift.inverse 1 (x/(2*Real.pi))=F⁻¹ x/(2*Real.pi) := by
  apply F.unitLift.strictMono.injective
  have h := F.unitLift.interpolate_inverse 1 (x/(2*Real.pi))
  rw [PositiveCircleGeometry.SmoothLift.interpolate_one] at h
  rw [h,F.unitLift_apply,mul_div_cancel₀ _ (by positivity : (2*Real.pi:ℝ) ≠ 0),F.apply_inv_apply]
lemma unitLift_density_one (g : ℝ → ℝ) (k : ℕ) (x : ℝ) :
    F.unitLift.density (fun t => g (2*Real.pi*t)) k 1 (x/(2*Real.pi))=
      (deriv F (F⁻¹ x))^k*g (F⁻¹ x) := by
  rw [PositiveCircleGeometry.SmoothLift.density,F.unitLift_inverse_one]
  simp only [PositiveCircleGeometry.SmoothLift.jacobian,Real.smoothTransition.one,
    sub_self,zero_add,one_mul]
  change deriv F.unitParameter (F⁻¹ x/(2*Real.pi))^k*g (2*Real.pi*(F⁻¹ x/(2*Real.pi)))=_
  rw [(F.unitParameter_derivative _).deriv,mul_div_cancel₀ _ (by positivity : (2*Real.pi:ℝ) ≠ 0)]
end StronglyRationalVOA.SmoothCircleLift
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

def diffeomorphismImplementer (hc : A.toVertexAlgebra.C2Cofinite) (F : SmoothCircleLift) :
    Completion V ≃ₗᵢ[ℂ] Completion V :=
  U.stressPropagatorEquiv hc F.unitLift.angularStressPath 1
lemma diffeomorphism_primary_closed_covariance (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {k : ℕ} (ha : a ∈ A.grade (k+1)) (hpa : A.IsPrimary a) (hh : U.IsHermitian (k+1) a)
    (F : SmoothCircleLift) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : Function.Periodic g 1) :
    OperatorTransport.transport (U.diffeomorphismImplementer hc F)
      (U.closedSmoothField hc a (k+1) (F.unitLift.angularDensity g hg hp k 1)) =
      U.closedSmoothField hc a (k+1) (F.unitLift.angularDensity g hg hp k 0) :=
  U.primary_density_closed_covariance hc ha hpa hh F.unitLift g hg hp 1
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open scoped ContDiff
namespace StronglyRationalVOA.SmoothCircleLift
lemma derivative_periodic (F : SmoothCircleLift) : Function.Periodic (deriv F) (2*Real.pi) := by
  intro x
  have h : (fun y => F (y+2*Real.pi))=(fun y => F y+2*Real.pi) := funext F.period
  have he := congrFun (congrArg deriv h) x
  simpa only [deriv_comp_add_const,deriv_add_const] using he
lemma derivative_mul (F G : SmoothCircleLift) (x : ℝ) :
    deriv (fun y => (F*G) y) x=deriv F (G x)*deriv G x :=
  (((F.differentiable (G x)).hasDerivAt).comp x (G.differentiable x).hasDerivAt).deriv
 
def pushDensity (F : SmoothCircleLift) (k : ℕ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv F (F⁻¹ x)^k*g (F⁻¹ x)
lemma pushDensity_smooth (F : SmoothCircleLift) (k : ℕ) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (F.pushDensity k g) :=
  (((contDiff_infty_iff_deriv.mp F.smooth).2.comp (F⁻¹).smooth).pow k).mul
    (hg.comp (F⁻¹).smooth)
lemma pushDensity_periodic (F : SmoothCircleLift) (k : ℕ) {g : ℝ → ℝ}
    (hp : Function.Periodic g (2*Real.pi)) : Function.Periodic (F.pushDensity k g) (2*Real.pi) := by
  intro x
  dsimp only [pushDensity]
  rw [(F⁻¹).period,F.derivative_periodic,hp]
lemma pushDensity_pos (F : SmoothCircleLift) (k : ℕ) {g : ℝ → ℝ}
    (hg : ∀ x, 0 < g x) (x : ℝ) : 0 < F.pushDensity k g x :=
  mul_pos (pow_pos (F.derivative_positive _) k) (hg _)
lemma pushDensity_one (k : ℕ) (g : ℝ → ℝ) : (1 : SmoothCircleLift).pushDensity k g=g := by
  funext x
  simp only [pushDensity,inv_one,one_apply]
  have h : deriv (fun x : ℝ => x) x=1 := deriv_id x
  change deriv (fun x : ℝ => x) x^k*g x=g x
  rw [h,one_pow,one_mul]
lemma pushDensity_mul (F G : SmoothCircleLift) (k : ℕ) (g : ℝ → ℝ) :
    (F*G).pushDensity k g=F.pushDensity k (G.pushDensity k g) := by
  funext x
  dsimp only [pushDensity]
  rw [mul_inv_rev,mul_apply,derivative_mul,apply_inv_apply,mul_pow]
  ring
lemma pushDensity_inverse (F : SmoothCircleLift) (k : ℕ) (g : ℝ → ℝ) :
    F⁻¹.pushDensity k (F.pushDensity k g)=g := by
  rw [← pushDensity_mul,inv_mul_cancel,pushDensity_one]
end StronglyRationalVOA.SmoothCircleLift

open UniformSpace
open scoped ContDiff
namespace StronglyRationalVOA.SmoothCircleLift
variable (F : SmoothCircleLift) (g : ℝ → ℝ)
def unitTest (x : ℝ) : ℝ := g (2*Real.pi*x)
lemma unitTest_smooth (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (unitTest g) :=
  hg.comp (contDiff_const.mul contDiff_id)
lemma unitTest_periodic (hp : Function.Periodic g (2*Real.pi)) : Function.Periodic (unitTest g) 1 := by
  intro x
  dsimp only [unitTest]
  rw [mul_add,mul_one,hp]
def pushedTest (k : ℕ) (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g (2*Real.pi)) : SmoothCircleFunction :=
  SmoothCircleFunction.ofRealPeriodic (F.pushDensity k g) (F.pushDensity_periodic k hp) (F.pushDensity_smooth k hg)
lemma angularTest_zero (k : ℕ) (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g (2*Real.pi)) :
    F.unitLift.angularDensity (unitTest g) (unitTest_smooth g hg) (unitTest_periodic g hp) k 0=
      SmoothCircleFunction.ofRealPeriodic g hp hg := by
  ext x
  change (F.unitLift.density (unitTest g) k 0 (x/(2*Real.pi)):ℂ)=(g x:ℂ)
  rw [PositiveCircleGeometry.SmoothLift.density_zero]
  dsimp only [unitTest]
  rw [mul_div_cancel₀ _ (by positivity : (2*Real.pi:ℝ) ≠ 0)]
lemma angularTest_one (k : ℕ) (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g (2*Real.pi)) :
    F.unitLift.angularDensity (unitTest g) (unitTest_smooth g hg) (unitTest_periodic g hp) k 1=
      F.pushedTest g k hg hp := by
  ext x
  exact congrArg Complex.ofReal (F.unitLift_density_one g k x)
def anomaly (c : ℂ) : ℂ := c/24 * (((2*Real.pi)⁻¹ *
  (RealCircleCalculus.anomalyEnergy (2*Real.pi) (F.pushDensity 1 g)-
    RealCircleCalculus.anomalyEnergy (2*Real.pi) g) : ℝ) : ℂ)
lemma anomaly_endpoint (c : ℂ) :
    F.unitLift.anomalyShift (unitTest g) c 1=F.anomaly g c := by
  have h0 : (fun x => F.unitLift.realAngularDensity (unitTest g) 1 (0,x))=g := by
    funext x
    change F.unitLift.density (unitTest g) 1 0 (x/(2*Real.pi))=g x
    rw [PositiveCircleGeometry.SmoothLift.density_zero]
    dsimp only [unitTest]
    rw [mul_div_cancel₀ _ (by positivity : (2*Real.pi:ℝ) ≠ 0)]
  have h1 : (fun x => F.unitLift.realAngularDensity (unitTest g) 1 (1,x))=F.pushDensity 1 g := by
    funext x
    exact F.unitLift_density_one g 1 x
  simp only [PositiveCircleGeometry.SmoothLift.anomalyShift,
    PositiveCircleGeometry.SmoothLift.normalizedAnomaly,h0,h1,anomaly,mul_sub]
lemma anomaly_mul (G : SmoothCircleLift) (c : ℂ) :
    (F*G).anomaly g c=F.anomaly (G.pushDensity 1 g) c+G.anomaly g c := by
  simp only [anomaly,pushDensity_mul]
  push_cast
  ring
end StronglyRationalVOA.SmoothCircleLift
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
def diffeomorphismSmoothImplementer (hc : A.toVertexAlgebra.C2Cofinite) (F : SmoothCircleLift) :
    U.smoothEnergySpace ≃ₗᵢ[ℂ] U.smoothEnergySpace :=
  U.stressPropagatorSmoothEquiv hc F.unitLift.angularStressPath 1
lemma diffeomorphism_primary_smooth (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {k : ℕ} (ha : a ∈ A.grade (k+1)) (hpa : A.IsPrimary a) (hh : U.IsHermitian (k+1) a)
    (F : SmoothCircleLift) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : Function.Periodic g (2*Real.pi)) (y : U.smoothEnergySpace) :
    U.smoothSmear hc ha (F.pushedTest g k hg hp).rapid_coefficients
      (U.diffeomorphismSmoothImplementer hc F y)=
    U.diffeomorphismSmoothImplementer hc F
      (U.smoothSmear hc ha (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients y) := by
  apply Subtype.ext
  have h := U.primary_density_smooth_covariance hc ha hpa hh F.unitLift
    (SmoothCircleLift.unitTest g) (SmoothCircleLift.unitTest_smooth g hg)
    (SmoothCircleLift.unitTest_periodic g hp) 1 y
  rw [F.angularTest_zero,F.angularTest_one] at h
  exact h
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
