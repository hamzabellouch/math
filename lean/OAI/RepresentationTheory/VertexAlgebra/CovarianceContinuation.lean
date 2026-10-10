import OAI.RepresentationTheory.VertexAlgebra.DiffeomorphismContinuity

namespace OAI

noncomputable section
open UniformSpace Set
open scoped ContDiff Topology
namespace StronglyRationalVOA.SmoothCircleLift
 
def pushTest (F : SmoothCircleLift) (k : ℕ) (f : SmoothCircleFunction) : SmoothCircleFunction where
  toFun x := (deriv F (F⁻¹ x)^k : ℝ) * f (F⁻¹ x)
  periodic x := by
    dsimp only
    rw [(F⁻¹).period,F.derivative_periodic,f.periodic]
  smooth := (Complex.ofRealCLM.contDiff.comp
    (((contDiff_infty_iff_deriv.mp F.smooth).2.comp (F⁻¹).smooth).pow k)).mul
      (f.smooth.comp (F⁻¹).smooth)
lemma pushTest_realPeriodic (F : SmoothCircleLift) (k : ℕ) (g : ℝ → ℝ)
    (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g (2*Real.pi)) :
    F.pushTest k (SmoothCircleFunction.ofRealPeriodic g hp hg)=F.pushedTest g k hg hp := by
  ext x
  exact (Complex.ofReal_mul _ _).symm
lemma pushTest_add (F : SmoothCircleLift) (k : ℕ) (f g : SmoothCircleFunction) :
    F.pushTest k (f.add g)=(F.pushTest k f).add (F.pushTest k g) := by
  ext x
  exact mul_add _ _ _
lemma pushTest_support (F : SmoothCircleLift) (k : ℕ) (f : SmoothCircleFunction) :
    tsupport (F.pushTest k f).onCircle ⊆ F.onCircle '' tsupport f.onCircle := by
  have he : F.onCircle '' tsupport f.onCircle =
      F⁻¹.onCircle ⁻¹' tsupport f.onCircle := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa only [Set.mem_preimage,F.onCircle_inverse] using hy
    · intro hx
      refine ⟨F⁻¹.onCircle x,hx,?_⟩
      simpa using F⁻¹.onCircle_inverse x
  rw [he]
  apply closure_minimal _ (isClosed_closure.preimage F⁻¹.continuous_onCircle)
  intro x hx
  apply subset_closure
  induction x using QuotientAddGroup.induction_on with
  | H x =>
    change f.onCircle ((F⁻¹ x : ℝ) : AddCircle (2*Real.pi)) ≠ 0
    change ((deriv F (F⁻¹ x)^k : ℝ) : ℂ)*f (F⁻¹ x) ≠ 0 at hx
    exact fun hz => hx (by rw [show f (F⁻¹ x)=0 from hz,mul_zero])
 
def mapArc (F : SmoothCircleLift) (I : ProperCircleArc) : ProperCircleArc where
  left := F I.left
  right := F I.right
  nonempty' := F.toOrderIso.strictMono I.nonempty'
  nondense' := by simpa only [F.period] using F.toOrderIso.strictMono I.nondense'
lemma mapArc_carrier (F : SmoothCircleLift) (I : ProperCircleArc) :
    (F.mapArc I).carrier=F.onCircle '' I.carrier := by
  ext x
  constructor
  · rintro ⟨t,ht,rfl⟩
    refine ⟨((F⁻¹ t : ℝ) : AddCircle (2*Real.pi)),⟨F⁻¹ t,?_,rfl⟩,?_⟩
    · exact ⟨F.toOrderIso.lt_symm_apply.mpr ht.1,F.toOrderIso.symm_apply_lt.mpr ht.2⟩
    · simp only [onCircle_coe,apply_inv_apply]
  · rintro ⟨y,⟨t,ht,rfl⟩,rfl⟩
    exact ⟨F t,⟨F.toOrderIso.strictMono ht.1,F.toOrderIso.strictMono ht.2⟩,rfl⟩
end StronglyRationalVOA.SmoothCircleLift

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma diffeomorphism_primary_test_smooth (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a) (hh : U.IsHermitian d a)
    (hd : 0 < d) (F : SmoothCircleLift) (f : SmoothCircleFunction) (hf : f.IsReal)
    (y : U.smoothEnergySpace) :
    U.smoothSmear hc ha (F.pushTest (d-1) f).rapid_coefficients
      (U.diffeomorphismSmoothImplementer hc F y)=
      U.diffeomorphismSmoothImplementer hc F (U.smoothSmear hc ha f.rapid_coefficients y) := by
  cases d with
  | zero => omega
  | succ k =>
    have h := U.diffeomorphism_primary_smooth hc (k := k) ha hp hh F (fun x => (f x).re)
      (Complex.reCLM.contDiff.comp f.smooth) (fun x => congrArg Complex.re (f.periodic x)) y
    have he := F.pushTest_realPeriodic k (fun x => (f x).re)
      (Complex.reCLM.contDiff.comp f.smooth) (fun x => congrArg Complex.re (f.periodic x))
    rw [← he,f.real_reconstruct hf] at h
    exact h
 

lemma diffeomorphism_stress_test_smooth (hc : A.toVertexAlgebra.C2Cofinite)
    (F : SmoothCircleLift) (f : SmoothCircleFunction) (hf : f.IsReal) :
    ∃ c : ℂ, ∀ y : U.smoothEnergySpace,
    U.smoothSmear hc A.conformal_mem (F.pushTest 1 f).rapid_coefficients
      (U.diffeomorphismSmoothImplementer hc F y)=
      U.diffeomorphismSmoothImplementer hc F (U.smoothSmear hc A.conformal_mem f.rapid_coefficients y)+
        c • U.diffeomorphismSmoothImplementer hc F y := by
  let g : ℝ → ℝ := fun x => (f x).re
  have hg : ContDiff ℝ ∞ g := Complex.reCLM.contDiff.comp f.smooth
  have hp : Function.Periodic g (2*Real.pi) := fun x => congrArg Complex.re (f.periodic x)
  obtain ⟨M,hM,hb⟩ := (hp.isBounded_of_continuous (by positivity) hg.continuous).exists_pos_norm_le
  have hpos (x : ℝ) : 0 < g x+(M+1) := by
    have H := hb (g x) ⟨x,rfl⟩
    rw [Real.norm_eq_abs] at H
    have := (abs_le.mp H).1
    linarith
  have hp' : Function.Periodic (fun x => g x+(M+1)) (2*Real.pi) :=
    fun x => congrArg (fun z : ℝ => z+(M+1)) (hp x)
  have hpM : Function.Periodic (fun _ : ℝ => M+1) (2*Real.pi) := fun _ => rfl
  refine ⟨F.anomaly (fun x => g x+(M+1)) A.centralCharge-
    F.anomaly (fun _ => M+1) A.centralCharge,?_⟩
  intro y
  have h := U.diffeomorphism_stress_smooth hc F (fun x => g x+(M+1))
    (hg.add contDiff_const) hp' hpos y
  have H := U.diffeomorphism_stress_smooth hc F (fun _ => M+1)
    contDiff_const hpM (fun _ => by linarith) y
  have he : SmoothCircleFunction.ofRealPeriodic (fun x => g x+(M+1)) hp' (hg.add contDiff_const)=
      f.add (SmoothCircleFunction.ofRealPeriodic (fun _ => M+1) hpM contDiff_const) := by
    rw [← f.real_reconstruct hf]
    ext x
    exact Complex.ofReal_add _ _
  rw [← F.pushTest_realPeriodic,he,F.pushTest_add,
    U.smoothSmear_add_functions,U.smoothSmear_add_functions,
    LinearMap.add_apply,LinearMap.add_apply,map_add] at h
  rw [← F.pushTest_realPeriodic] at H
  rw [H] at h
  rw [sub_smul]
  apply add_right_cancel (b := U.diffeomorphismSmoothImplementer hc F
    (U.smoothSmear hc A.conformal_mem
      (SmoothCircleFunction.ofRealPeriodic (fun _ => M+1) hpM contDiff_const).rapid_coefficients y)+
      F.anomaly (fun _ => M+1) A.centralCharge • U.diffeomorphismSmoothImplementer hc F y)
  exact h.trans (by abel)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
