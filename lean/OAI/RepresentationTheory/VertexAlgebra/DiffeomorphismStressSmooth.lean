import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.RotationConjugateCommutant

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
lemma diffeomorphism_stress_smooth (hc : A.toVertexAlgebra.C2Cofinite)
    (F : SmoothCircleLift) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : Function.Periodic g (2*Real.pi)) (hpos : ∀ x, 0 < g x) (y : U.smoothEnergySpace) :
    U.smoothSmear hc A.conformal_mem (F.pushedTest g 1 hg hp).rapid_coefficients
      (U.diffeomorphismSmoothImplementer hc F y)=
    U.diffeomorphismSmoothImplementer hc F
      (U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients y)+
      F.anomaly g A.centralCharge • U.diffeomorphismSmoothImplementer hc F y := by
  apply Subtype.ext
  have h := U.stress_density_smooth_covariance hc F.unitLift
    (SmoothCircleLift.unitTest g) (SmoothCircleLift.unitTest_smooth g hg)
    (SmoothCircleLift.unitTest_periodic g hp) (fun x => hpos (2*Real.pi*x)) 1 y
  rw [F.angularTest_zero,F.angularTest_one,F.anomaly_endpoint] at h
  exact h
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
open scoped ContDiff
namespace StronglyRationalVOA.SmoothCircleLift
lemma pushedTest_mul (F G : SmoothCircleLift) (k : ℕ) (g : ℝ → ℝ)
    (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g (2*Real.pi)) :
    F.pushedTest (G.pushDensity k g) k (G.pushDensity_smooth k hg) (G.pushDensity_periodic k hp)=
      (F*G).pushedTest g k hg hp := by
  ext x
  exact congrArg (fun f : ℝ → ℝ => (f x:ℂ)) (F.pushDensity_mul G k g).symm
end StronglyRationalVOA.SmoothCircleLift
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 
def diffeomorphismDefect (hc : A.toVertexAlgebra.C2Cofinite) (F G : SmoothCircleLift) :
    Completion V ≃ₗᵢ[ℂ] Completion V :=
  ((U.diffeomorphismImplementer hc G).trans (U.diffeomorphismImplementer hc F)).trans
    (U.diffeomorphismImplementer hc (F*G)).symm
def diffeomorphismSmoothDefect (hc : A.toVertexAlgebra.C2Cofinite) (F G : SmoothCircleLift) :
    U.smoothEnergySpace ≃ₗᵢ[ℂ] U.smoothEnergySpace :=
  ((U.diffeomorphismSmoothImplementer hc G).trans (U.diffeomorphismSmoothImplementer hc F)).trans
    (U.diffeomorphismSmoothImplementer hc (F*G)).symm
lemma diffeomorphism_defect_primary (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {k : ℕ} (ha : a ∈ A.grade (k+1)) (hpa : A.IsPrimary a) (hh : U.IsHermitian (k+1) a)
    (F G : SmoothCircleLift) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : Function.Periodic g (2*Real.pi)) (y : U.smoothEnergySpace) :
    U.smoothSmear hc ha (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients
      (U.diffeomorphismSmoothDefect hc F G y)=
    U.diffeomorphismSmoothDefect hc F G
      (U.smoothSmear hc ha (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients y) := by
  let Ef := U.diffeomorphismSmoothImplementer hc F
  let Eg := U.diffeomorphismSmoothImplementer hc G
  let E := U.diffeomorphismSmoothImplementer hc (F*G)
  let T := U.smoothSmear hc ha (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients
  let Tp := U.smoothSmear hc ha ((F*G).pushedTest g k hg hp).rapid_coefficients
  have hprod : Tp (Ef (Eg y))=Ef (Eg (T y)) := by
    have h := U.diffeomorphism_primary_smooth hc ha hpa hh F (G.pushDensity k g)
      (G.pushDensity_smooth k hg) (G.pushDensity_periodic k hp) (Eg y)
    dsimp only [Eg] at h
    rw [F.pushedTest_mul] at h
    change Tp (Ef (Eg y))=Ef (U.smoothSmear hc ha (G.pushedTest g k hg hp).rapid_coefficients (Eg y)) at h
    have hG := U.diffeomorphism_primary_smooth hc ha hpa hh G g hg hp y
    change U.smoothSmear hc ha (G.pushedTest g k hg hp).rapid_coefficients (Eg y)=Eg (T y) at hG
    rw [hG] at h
    exact h
  have hE := U.diffeomorphism_primary_smooth hc ha hpa hh (F*G) g hg hp
    (E.symm (Ef (Eg y)))
  change Tp (E (E.symm (Ef (Eg y))))=E (T (E.symm (Ef (Eg y)))) at hE
  rw [E.apply_symm_apply,hprod] at hE
  apply E.injective
  change E (T (E.symm (Ef (Eg y))))=E (E.symm (Ef (Eg (T y))))
  rw [E.apply_symm_apply]
  exact hE.symm
lemma diffeomorphism_defect_positive_stress (hc : A.toVertexAlgebra.C2Cofinite)
    (F G : SmoothCircleLift) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : Function.Periodic g (2*Real.pi)) (hpos : ∀ x, 0 < g x) (y : U.smoothEnergySpace) :
    U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients
      (U.diffeomorphismSmoothDefect hc F G y)=
    U.diffeomorphismSmoothDefect hc F G
      (U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients y) := by
  let Ef := U.diffeomorphismSmoothImplementer hc F
  let Eg := U.diffeomorphismSmoothImplementer hc G
  let E := U.diffeomorphismSmoothImplementer hc (F*G)
  let T := U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients
  let Tp := U.smoothSmear hc A.conformal_mem ((F*G).pushedTest g 1 hg hp).rapid_coefficients
  have hprod : Tp (Ef (Eg y))=Ef (Eg (T y))+(F*G).anomaly g A.centralCharge • Ef (Eg y) := by
    have h := U.diffeomorphism_stress_smooth hc F (G.pushDensity 1 g)
      (G.pushDensity_smooth 1 hg) (G.pushDensity_periodic 1 hp) (G.pushDensity_pos 1 hpos) (Eg y)
    dsimp only [Eg] at h
    rw [F.pushedTest_mul] at h
    change Tp (Ef (Eg y))=Ef (U.smoothSmear hc A.conformal_mem (G.pushedTest g 1 hg hp).rapid_coefficients (Eg y))+
      F.anomaly (G.pushDensity 1 g) A.centralCharge • Ef (Eg y) at h
    have hG := U.diffeomorphism_stress_smooth hc G g hg hp hpos y
    change U.smoothSmear hc A.conformal_mem (G.pushedTest g 1 hg hp).rapid_coefficients (Eg y)=Eg (T y)+
      G.anomaly g A.centralCharge • Eg y at hG
    rw [hG,map_add,map_smul] at h
    rw [F.anomaly_mul]
    rw [add_smul]
    exact h.trans (by abel)
  have hE := U.diffeomorphism_stress_smooth hc (F*G) g hg hp hpos
    (E.symm (Ef (Eg y)))
  change Tp (E (E.symm (Ef (Eg y))))=E (T (E.symm (Ef (Eg y))))+
    (F*G).anomaly g A.centralCharge • E (E.symm (Ef (Eg y))) at hE
  rw [E.apply_symm_apply,hprod] at hE
  have hcancel := add_right_cancel hE
  apply E.injective
  change E (T (E.symm (Ef (Eg y))))=E (E.symm (Ef (Eg (T y))))
  rw [E.apply_symm_apply]
  exact hcancel.symm
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
open scoped ContDiff
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma diffeomorphism_defect_stress (hc : A.toVertexAlgebra.C2Cofinite)
    (F G : SmoothCircleLift) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : Function.Periodic g (2*Real.pi)) (y : U.smoothEnergySpace) :
    U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients
      (U.diffeomorphismSmoothDefect hc F G y)=
    U.diffeomorphismSmoothDefect hc F G
      (U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients y) := by
  obtain ⟨M,hM,hb⟩ := (hp.isBounded_of_continuous (by positivity) hg.continuous).exists_pos_norm_le
  have hpos (x : ℝ) : 0 < g x+(M+1) := by
    have H := hb (g x) ⟨x,rfl⟩
    rw [Real.norm_eq_abs] at H
    have := (abs_le.mp H).1
    linarith
  have hp' : Function.Periodic (fun x => g x+(M+1)) (2*Real.pi) := by
    intro x; exact congrArg (fun z : ℝ => z+(M+1)) (hp x)
  have hpM : Function.Periodic (fun _ : ℝ => M+1) (2*Real.pi) := fun _ => rfl
  have h := U.diffeomorphism_defect_positive_stress hc F G (fun x => g x+(M+1))
    (hg.add contDiff_const) hp' hpos y
  have hM' := U.diffeomorphism_defect_positive_stress hc F G (fun _ => M+1)
    contDiff_const hpM (fun _ => by linarith) y
  have he : SmoothCircleFunction.ofRealPeriodic (fun x => g x+(M+1)) hp' (hg.add contDiff_const)=
      (SmoothCircleFunction.ofRealPeriodic g hp hg).add
        (SmoothCircleFunction.ofRealPeriodic (fun _ => M+1) hpM contDiff_const) := by
    ext x
    exact Complex.ofReal_add _ _
  rw [he,U.smoothSmear_add_functions,LinearMap.add_apply,LinearMap.add_apply,map_add,hM'] at h
  exact add_right_cancel h
lemma diffeomorphism_defect_primary_test (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a) (hh : U.IsHermitian d a)
    (hd : 0 < d) (F G : SmoothCircleLift) (f : SmoothCircleFunction) (hf : f.IsReal)
    (y : U.smoothEnergySpace) :
    U.smoothSmear hc ha f.rapid_coefficients (U.diffeomorphismSmoothDefect hc F G y)=
      U.diffeomorphismSmoothDefect hc F G (U.smoothSmear hc ha f.rapid_coefficients y) := by
  cases d with
  | zero => omega
  | succ k =>
    have h := U.diffeomorphism_defect_primary hc ha hp hh F G (fun x => (f x).re)
      (Complex.reCLM.contDiff.comp f.smooth) (fun x => congrArg Complex.re (f.periodic x)) y
    rwa [f.real_reconstruct hf] at h
lemma diffeomorphism_defect_test (hc : A.toVertexAlgebra.C2Cofinite)
    (F G : SmoothCircleLift) (T : U.PrimaryTestField) (y : U.smoothEnergySpace) :
    U.smoothSmear hc T.homogeneous T.test.rapid_coefficients
      (U.diffeomorphismSmoothDefect hc F G y)=
      U.diffeomorphismSmoothDefect hc F G (U.smoothSmear hc T.homogeneous T.test.rapid_coefficients y) := by
  rcases T.kind with hw | ⟨hw,ha⟩ | ⟨hp,hd,_⟩
  · have hp : A.IsPrimary T.state := by
      intro n hn
      by_cases h : n=1
      · subst n; exact T.quasiPrimary
      · exact A.virasoro_eq_zero_of_lt (hw ▸ T.homogeneous) n (by omega)
    exact U.diffeomorphism_defect_primary_test hc T.homogeneous hp T.hermitian
      (by omega) F G T.test T.real y
  · have h := U.diffeomorphism_defect_stress hc F G (fun x => (T.test x).re)
      (Complex.reCLM.contDiff.comp T.test.smooth) (fun x => congrArg Complex.re (T.test.periodic x)) y
    rw [T.test.real_reconstruct T.real] at h
    simpa only [hw,ha] using h
  · exact U.diffeomorphism_defect_primary_test hc T.homogeneous hp T.hermitian
      (by omega) F G T.test T.real y
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma diffeomorphismSmoothDefect_coe (hc : A.toVertexAlgebra.C2Cofinite)
    (F G : SmoothCircleLift) (x : U.smoothEnergySpace) :
    (U.diffeomorphismSmoothDefect hc F G x : Completion V)=U.diffeomorphismDefect hc F G x := rfl
lemma diffeomorphismSmoothDefect_symm_coe (hc : A.toVertexAlgebra.C2Cofinite)
    (F G : SmoothCircleLift) (x : U.smoothEnergySpace) :
    ((U.diffeomorphismSmoothDefect hc F G).symm x : Completion V)=
      (U.diffeomorphismDefect hc F G).symm x := rfl
lemma diffeomorphism_defect_closed (hc : A.toVertexAlgebra.C2Cofinite)
    (F G : SmoothCircleLift) (T : U.PrimaryTestField) :
    OperatorTransport.transport (U.diffeomorphismDefect hc F G) (T.field hc)=T.field hc := by
  let E := U.diffeomorphismDefect hc F G
  let e := U.diffeomorphismSmoothDefect hc F G
  have hE (x : Completion V) (hx : x ∈ U.smoothEnergySpace) : E x ∈ U.smoothEnergySpace :=
    (e ⟨x,hx⟩).property
  have hI (x : Completion V) (hx : x ∈ U.smoothEnergySpace) : E.symm x ∈ U.smoothEnergySpace :=
    (e.symm ⟨x,hx⟩).property
  have h := OperatorTransport.onSubmodule E U.smoothEnergySpace
    (U.smoothSmear hc T.homogeneous T.test.rapid_coefficients)
    (U.smoothSmear hc T.homogeneous T.test.rapid_coefficients) hE hI
    (fun x => congrArg Subtype.val (U.diffeomorphism_defect_test hc F G T x))
  have H := congrArg LinearPMap.closure h
  rw [OperatorTransport.closure E (U.smoothSmear_core_closable hc T.homogeneous T.test.rapid_coefficients),
    U.smoothSmear_core hc T.homogeneous] at H
  exact H
 

theorem diffeomorphism_defect_scalar (hc : A.toVertexAlgebra.C2Cofinite)
    (F G : SmoothCircleLift) : ∃ c : ℂ,
    (U.diffeomorphismDefect hc F G).toContinuousLinearEquiv.toContinuousLinearMap=c • (1 : Completion V →L[ℂ] Completion V) := by
  apply U.global_commutant_scalar hc
  rw [U.localAlgebra_eq_primaryAlgebra hc isOpen_univ,← SetLike.mem_coe,
    primaryAlgebra,LocalOperatorAlgebra.coe_generated_commutant]
  have hdata : ∀ B ∈ U.primaryGraphData hc Set.univ,
      B*(U.diffeomorphismDefect hc F G).toContinuousLinearEquiv.toContinuousLinearMap=
        (U.diffeomorphismDefect hc F G).toContinuousLinearEquiv.toContinuousLinearMap*B := by
    rintro B ⟨T,_,i,j,rfl⟩
    apply ContinuousLinearMap.ext
    intro x
    have h := ClosedGraphData.entry_transport (U.diffeomorphismDefect hc F G) (T.field hc) (T.closed hc) i j x
    simp only [U.diffeomorphism_defect_closed hc F G T] at h
    have H := congrArg (U.diffeomorphismDefect hc F G) h
    rw [LinearIsometryEquiv.apply_symm_apply] at H
    exact H.symm
  intro B hB
  rcases hB with hB | hB
  · exact hdata B hB
  · apply hdata B
    obtain ⟨T,hT,i,j,he⟩ := hB
    refine ⟨T,hT,j,i,?_⟩
    have H := congrArg star he
    rw [star_star,ClosedGraphData.star_entry] at H
    exact H
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
include U in
lemma scalarUnitary_norm (E : Completion V ≃ₗᵢ[ℂ] Completion V) {c : ℂ}
    (h : E.toContinuousLinearEquiv.toContinuousLinearMap=c • (1 : Completion V →L[ℂ] Completion V)) :
    ‖c‖=1 := by
  have hv : ‖(A.vacuum : Completion V)‖=1 := by simpa only [Completion.norm_coe] using U.vacuum_norm
  have H := congrArg (fun Q : Completion V →L[ℂ] Completion V => ‖Q (A.vacuum : Completion V)‖) h
  change ‖E (A.vacuum : Completion V)‖=‖c • (A.vacuum : Completion V)‖ at H
  rw [E.norm_map,norm_smul,hv,mul_one] at H
  exact H.symm
 

theorem diffeomorphism_projective_mul (hc : A.toVertexAlgebra.C2Cofinite)
    (F G : SmoothCircleLift) : ∃ c : ℂ, ‖c‖=1 ∧ ∀ x : Completion V,
    U.diffeomorphismImplementer hc F (U.diffeomorphismImplementer hc G x)=
      c • U.diffeomorphismImplementer hc (F*G) x := by
  obtain ⟨c,hc'⟩ := U.diffeomorphism_defect_scalar hc F G
  refine ⟨c,U.scalarUnitary_norm _ hc',?_⟩
  intro x
  have h := congrArg (fun Q : Completion V →L[ℂ] Completion V => Q x) hc'
  change (U.diffeomorphismImplementer hc (F*G)).symm
    (U.diffeomorphismImplementer hc F (U.diffeomorphismImplementer hc G x))=c • x at h
  have H := congrArg (U.diffeomorphismImplementer hc (F*G)) h
  simpa only [LinearIsometryEquiv.apply_symm_apply,map_smul] using H
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA
 
def scalarPhaseSubgroup (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Subgroup (H ≃ₗᵢ[ℂ] H) where
  carrier := {E | ∃ c : ℂ, ‖c‖=1 ∧ ∀ x : H, E x=c • x}
  one_mem' := ⟨1,by simp,fun x => (one_smul ℂ x).symm⟩
  mul_mem' := by
    rintro E F ⟨c,hc,he⟩ ⟨d,hd,hf⟩
    refine ⟨c*d,by rw [norm_mul,hc,hd,one_mul],?_⟩
    intro x
    change E (F x)=(c*d) • x
    rw [hf,he,mul_smul]
  inv_mem' := by
    rintro E ⟨c,hc,he⟩
    have hn : c ≠ 0 := by intro h; rw [h,norm_zero] at hc; norm_num at hc
    refine ⟨c⁻¹,by rw [norm_inv,hc,inv_one],?_⟩
    intro x
    apply E.injective
    change E (E.symm x)=E (c⁻¹ • x)
    rw [E.apply_symm_apply,map_smul,he,smul_smul,inv_mul_cancel₀ hn,one_smul]
instance scalarPhaseSubgroup_normal (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    (scalarPhaseSubgroup H).Normal where
  conj_mem := by
    rintro E ⟨c,hc,he⟩ F
    refine ⟨c,hc,?_⟩
    intro x
    change F (E (F.symm x))=c • x
    rw [he,map_smul,F.apply_symm_apply]
 

abbrev ProjectiveUnitaryGroup (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  (H ≃ₗᵢ[ℂ] H) ⧸ scalarPhaseSubgroup H
namespace CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

def liftProjectiveRepresentation (hc : A.toVertexAlgebra.C2Cofinite) :
    SmoothCircleLift →* ProjectiveUnitaryGroup (Completion V) :=
  MonoidHom.mk' (fun F => QuotientGroup.mk (U.diffeomorphismImplementer hc F)) (by
    intro F G
    change QuotientGroup.mk (U.diffeomorphismImplementer hc (F*G))=
      QuotientGroup.mk (U.diffeomorphismImplementer hc F)*QuotientGroup.mk (U.diffeomorphismImplementer hc G)
    rw [← QuotientGroup.mk_mul]
    apply QuotientGroup.eq.mpr
    obtain ⟨c,h⟩ := U.diffeomorphism_defect_scalar hc F G
    refine ⟨c,U.scalarUnitary_norm _ h,?_⟩
    intro x
    exact congrArg (fun Q : Completion V →L[ℂ] Completion V => Q x) h)
end CFTTypeVOA.UnitaryStructure
end StronglyRationalVOA

open UniformSpace
open scoped ContDiff
namespace StronglyRationalVOA.SmoothCircleLift
lemma rotation_inv (s : ℝ) : (rotation s)⁻¹=rotation (-s) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← rotation_add,add_neg_cancel,rotation_zero]
lemma derivative_rotation (s x : ℝ) : deriv (rotation s) x=1 := by
  exact ((hasDerivAt_id x).add_const s).deriv
lemma pushDensity_deck (n : ℤ) (k : ℕ) {g : ℝ → ℝ}
    (hp : Function.Periodic g (2*Real.pi)) :
    (rotation (n*(2*Real.pi))).pushDensity k g=g := by
  funext x
  simp only [pushDensity,rotation_inv,rotation_apply,derivative_rotation,one_pow,one_mul]
  have h := hp.zsmul (-n) x
  simpa only [zsmul_eq_mul,Int.cast_neg,neg_mul] using h
lemma pushedTest_deck (n : ℤ) (k : ℕ) (g : ℝ → ℝ)
    (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g (2*Real.pi)) :
    (rotation (n*(2*Real.pi))).pushedTest g k hg hp=SmoothCircleFunction.ofRealPeriodic g hp hg := by
  ext x
  exact congrArg Complex.ofReal (congrFun (pushDensity_deck n k hp) x)
lemma anomaly_deck (n : ℤ) (g : ℝ → ℝ) (hp : Function.Periodic g (2*Real.pi)) (c : ℂ) :
    (rotation (n*(2*Real.pi))).anomaly g c=0 := by
  simp only [anomaly,pushDensity_deck n 1 hp,sub_self,mul_zero,Complex.ofReal_zero]
end StronglyRationalVOA.SmoothCircleLift
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma positiveStress_commutation_extend (hc : A.toVertexAlgebra.C2Cofinite)
    (e : U.smoothEnergySpace ≃ₗᵢ[ℂ] U.smoothEnergySpace)
    (he : ∀ (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g (2*Real.pi)),
      (∀ x, 0 < g x) → ∀ y : U.smoothEnergySpace,
      U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients (e y)=
        e (U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients y))
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g (2*Real.pi))
    (y : U.smoothEnergySpace) :
    U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients (e y)=
        e (U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients y) := by
  obtain ⟨M,hM,hb⟩ := (hp.isBounded_of_continuous (by positivity) hg.continuous).exists_pos_norm_le
  have hpos (x : ℝ) : 0 < g x+(M+1) := by
    have H := hb (g x) ⟨x,rfl⟩
    rw [Real.norm_eq_abs] at H
    have := (abs_le.mp H).1
    linarith
  have hp' : Function.Periodic (fun x => g x+(M+1)) (2*Real.pi) := by
    intro x; exact congrArg (fun z : ℝ => z+(M+1)) (hp x)
  have hpM : Function.Periodic (fun _ : ℝ => M+1) (2*Real.pi) := fun _ => rfl
  have h := he (fun x => g x+(M+1)) (hg.add contDiff_const) hp' hpos y
  have hM' := he (fun _ => M+1) contDiff_const hpM (fun _ => by linarith) y
  have hsum : SmoothCircleFunction.ofRealPeriodic (fun x => g x+(M+1)) hp' (hg.add contDiff_const)=
      (SmoothCircleFunction.ofRealPeriodic g hp hg).add
        (SmoothCircleFunction.ofRealPeriodic (fun _ => M+1) hpM contDiff_const) := by
    ext x
    exact Complex.ofReal_add _ _
  rw [hsum,U.smoothSmear_add_functions,LinearMap.add_apply,LinearMap.add_apply,map_add,hM'] at h
  exact add_right_cancel h
lemma diffeomorphism_deck_primary (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a) (hh : U.IsHermitian d a)
    (hd : 0 < d) (n : ℤ) (f : SmoothCircleFunction) (hf : f.IsReal) (y : U.smoothEnergySpace) :
    U.smoothSmear hc ha f.rapid_coefficients
      (U.diffeomorphismSmoothImplementer hc (SmoothCircleLift.rotation (n*(2*Real.pi))) y)=
    U.diffeomorphismSmoothImplementer hc (SmoothCircleLift.rotation (n*(2*Real.pi)))
      (U.smoothSmear hc ha f.rapid_coefficients y) := by
  cases d with
  | zero => omega
  | succ k =>
    have h := U.diffeomorphism_primary_smooth hc ha hp hh
      (SmoothCircleLift.rotation (n*(2*Real.pi))) (fun x => (f x).re)
      (Complex.reCLM.contDiff.comp f.smooth) (fun x => congrArg Complex.re (f.periodic x)) y
    simpa only [SmoothCircleLift.pushedTest,SmoothCircleLift.pushDensity_deck n k (g := fun x => (f x).re)
      (fun x => congrArg Complex.re (f.periodic x)),f.real_reconstruct hf] using h
lemma diffeomorphism_deck_stress (hc : A.toVertexAlgebra.C2Cofinite)
    (n : ℤ) (f : SmoothCircleFunction) (hf : f.IsReal) (y : U.smoothEnergySpace) :
    U.smoothSmear hc A.conformal_mem f.rapid_coefficients
      (U.diffeomorphismSmoothImplementer hc (SmoothCircleLift.rotation (n*(2*Real.pi))) y)=
    U.diffeomorphismSmoothImplementer hc (SmoothCircleLift.rotation (n*(2*Real.pi)))
      (U.smoothSmear hc A.conformal_mem f.rapid_coefficients y) := by
  have he (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g (2*Real.pi))
      (hpos : ∀ x, 0 < g x) (y : U.smoothEnergySpace) :
      U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients
        (U.diffeomorphismSmoothImplementer hc (SmoothCircleLift.rotation (n*(2*Real.pi))) y)=
      U.diffeomorphismSmoothImplementer hc (SmoothCircleLift.rotation (n*(2*Real.pi)))
        (U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients y) := by
    have h := U.diffeomorphism_stress_smooth hc (SmoothCircleLift.rotation (n*(2*Real.pi))) g hg hp hpos y
    simpa only [SmoothCircleLift.pushedTest,SmoothCircleLift.pushDensity_deck n 1 hp,
      SmoothCircleLift.anomaly_deck n g hp,zero_smul,add_zero] using h
  have h := U.positiveStress_commutation_extend hc _ he (fun x => (f x).re)
    (Complex.reCLM.contDiff.comp f.smooth) (fun x => congrArg Complex.re (f.periodic x)) y
  rwa [f.real_reconstruct hf] at h
lemma diffeomorphism_deck_test (hc : A.toVertexAlgebra.C2Cofinite)
    (n : ℤ) (T : U.PrimaryTestField) (y : U.smoothEnergySpace) :
    U.smoothSmear hc T.homogeneous T.test.rapid_coefficients
      (U.diffeomorphismSmoothImplementer hc (SmoothCircleLift.rotation (n*(2*Real.pi))) y)=
    U.diffeomorphismSmoothImplementer hc (SmoothCircleLift.rotation (n*(2*Real.pi)))
      (U.smoothSmear hc T.homogeneous T.test.rapid_coefficients y) := by
  rcases T.kind with hw | ⟨hw,ha⟩ | ⟨hp,hd,_⟩
  · have hp : A.IsPrimary T.state := by
      intro j hj
      by_cases h : j=1
      · subst j; exact T.quasiPrimary
      · exact A.virasoro_eq_zero_of_lt (hw ▸ T.homogeneous) j (by omega)
    exact U.diffeomorphism_deck_primary hc T.homogeneous hp T.hermitian (by omega) n T.test T.real y
  · have h := U.diffeomorphism_deck_stress hc n T.test T.real y
    simpa only [hw,ha] using h
  · exact U.diffeomorphism_deck_primary hc T.homogeneous hp T.hermitian (by omega) n T.test T.real y
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma diffeomorphism_deck_closed (hc : A.toVertexAlgebra.C2Cofinite)
    (n : ℤ) (T : U.PrimaryTestField) :
    OperatorTransport.transport (U.diffeomorphismImplementer hc (SmoothCircleLift.rotation (n*(2*Real.pi))))
      (T.field hc)=T.field hc := by
  let F := SmoothCircleLift.rotation (n*(2*Real.pi))
  let E := U.diffeomorphismImplementer hc F
  let e := U.diffeomorphismSmoothImplementer hc F
  have hE (x : Completion V) (hx : x ∈ U.smoothEnergySpace) : E x ∈ U.smoothEnergySpace :=
    (e ⟨x,hx⟩).property
  have hI (x : Completion V) (hx : x ∈ U.smoothEnergySpace) : E.symm x ∈ U.smoothEnergySpace :=
    (e.symm ⟨x,hx⟩).property
  have h := OperatorTransport.onSubmodule E U.smoothEnergySpace
    (U.smoothSmear hc T.homogeneous T.test.rapid_coefficients)
    (U.smoothSmear hc T.homogeneous T.test.rapid_coefficients) hE hI
    (fun x => congrArg Subtype.val (U.diffeomorphism_deck_test hc n T x))
  have H := congrArg LinearPMap.closure h
  rw [OperatorTransport.closure E (U.smoothSmear_core_closable hc T.homogeneous T.test.rapid_coefficients),
    U.smoothSmear_core hc T.homogeneous] at H
  exact H
lemma diffeomorphism_deck_scalar (hc : A.toVertexAlgebra.C2Cofinite) (n : ℤ) : ∃ c : ℂ,
    (U.diffeomorphismImplementer hc (SmoothCircleLift.rotation (n*(2*Real.pi)))).toContinuousLinearEquiv.toContinuousLinearMap=
      c • (1 : Completion V →L[ℂ] Completion V) := by
  let E := U.diffeomorphismImplementer hc (SmoothCircleLift.rotation (n*(2*Real.pi)))
  apply U.global_commutant_scalar hc
  rw [U.localAlgebra_eq_primaryAlgebra hc isOpen_univ,← SetLike.mem_coe,
    primaryAlgebra,LocalOperatorAlgebra.coe_generated_commutant]
  have hdata : ∀ B ∈ U.primaryGraphData hc Set.univ,
      B*E.toContinuousLinearEquiv.toContinuousLinearMap=E.toContinuousLinearEquiv.toContinuousLinearMap*B := by
    rintro B ⟨T,_,i,j,rfl⟩
    apply ContinuousLinearMap.ext
    intro x
    have h := ClosedGraphData.entry_transport E (T.field hc) (T.closed hc) i j x
    dsimp only [E] at h
    simp only [U.diffeomorphism_deck_closed hc n T] at h
    have H := congrArg E h
    rw [LinearIsometryEquiv.apply_symm_apply] at H
    exact H.symm
  intro B hB
  rcases hB with hB | hB
  · exact hdata B hB
  · apply hdata B
    obtain ⟨T,hT,i,j,he⟩ := hB
    refine ⟨T,hT,j,i,?_⟩
    have H := congrArg star he
    rw [star_star,ClosedGraphData.star_entry] at H
    exact H
 

def diffeomorphismProjectiveRepresentation (hc : A.toVertexAlgebra.C2Cofinite) :
    SmoothCircleDiffeomorphism →* ProjectiveUnitaryGroup (Completion V) :=
  QuotientGroup.lift SmoothCircleLift.circleAction.ker (U.liftProjectiveRepresentation hc) (by
    intro F hF
    obtain ⟨n,rfl⟩ := (SmoothCircleLift.circleAction_kernel F).mp hF
    change QuotientGroup.mk (U.diffeomorphismImplementer hc (SmoothCircleLift.rotation (n*(2*Real.pi))))=1
    apply (QuotientGroup.eq_one_iff _).mpr
    obtain ⟨c,h⟩ := U.diffeomorphism_deck_scalar hc n
    refine ⟨c,U.scalarUnitary_norm _ h,?_⟩
    intro x
    exact congrArg (fun Q : Completion V →L[ℂ] Completion V => Q x) h)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter Set
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma stressCutoff_normalized_path_difference (hc : A.toVertexAlgebra.C2Cofinite)
    (n : ℕ) {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g)
    {r : ℕ} (hr : 1 ≤ r) :
    ‖(U.stressCutoff hc n hf-U.stressCutoff hc n hg)*U.inverseSobolev r‖ ≤
      coefficientSeminorm (fun k => f k-g k) 2*(1+A.centralCharge.re) := by
  rw [sub_mul,U.stressCutoff_normalized hc n hf hr,U.stressCutoff_normalized hc n hg hr,
    ← smul_sub,← sub_mul,← mul_sub,norm_smul,Complex.norm_I,one_mul]
  calc
    _ ≤ (‖U.energyCutoff n‖*‖U.stressNormalized hc hf r-U.stressNormalized hc hg r‖)*‖U.energyCutoff n‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1*‖U.stressNormalized hc hf r-U.stressNormalized hc hg r‖)*1 := by
      gcongr <;> exact U.energyCutoff_norm n
    _ ≤ _ := by simpa only [one_mul,mul_one] using U.stressNormalized_difference hc hf hg hr
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
