import OAI.RepresentationTheory.VertexAlgebra.MobiusAnomaly
import OAI.RepresentationTheory.VertexAlgebra.GraphCovariance

namespace OAI

noncomputable section
open UniformSpace Set
open scoped ContDiff MatrixGroups
namespace StronglyRationalVOA.CircleMobiusGeometry
lemma density_second (M : SL(2,ℝ)) (x : ℝ) :
    deriv (deriv (density M)) x= -cosine M*Real.cos x-sine M*Real.sin x := by
  rw [show deriv (density M)=(fun x => -cosine M*Real.sin x+sine M*Real.cos x) from
    funext (density_derivative M)]
  convert (((Real.hasDerivAt_sin x).const_mul (-cosine M)).add
    ((Real.hasDerivAt_cos x).const_mul (sine M))).deriv using 1
  first | rfl | ring
lemma density_third (M : SL(2,ℝ)) (x : ℝ) :
    iteratedDeriv 3 (density M) x= -deriv (density M) x := by
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  rw [show deriv (deriv (density M))=(fun x => -cosine M*Real.cos x-sine M*Real.sin x) from
    funext (density_second M)]
  rw [density_derivative]
  convert (((Real.hasDerivAt_cos x).const_mul (-cosine M)).sub
    ((Real.hasDerivAt_sin x).const_mul (sine M))).deriv using 1
  first | rfl | ring
lemma pushed_constant_mobius_equation (M : SL(2,ℝ)) (F : SmoothCircleLift) (hF : Implements M F) :
    ((F.pushedTest (fun _ => 1) 1 contDiff_const (fun _ => rfl)).differentiated 3).add
      ((F.pushedTest (fun _ => 1) 1 contDiff_const (fun _ => rfl)).differentiated 1)=
    SmoothCircleFunction.constant 0 := by
  ext x
  simp only [SmoothCircleFunction.add_apply,SmoothCircleFunction.differentiated_apply,
    SmoothCircleFunction.constant_apply]
  have he : (F.pushedTest (fun _ => 1) 1 contDiff_const (fun _ => rfl) : ℝ → ℂ)=
      fun x => (density M x : ℂ) := by
    funext x
    exact congrArg (fun g : ℝ → ℝ => (g x:ℂ)) (push_constant M F hF)
  rw [he,RealCircleCalculus.iteratedDeriv_ofReal (density_smooth M),
    RealCircleCalculus.iteratedDeriv_ofReal (density_smooth M)]
  dsimp only
  rw [density_third,iteratedDeriv_one]
  simp
end StronglyRationalVOA.CircleMobiusGeometry
namespace StronglyRationalVOA.SmoothCircleFunction
lemma coefficient_of_mobius_equation (f : SmoothCircleFunction)
    (hf : (f.differentiated 3).add (f.differentiated 1)=constant 0) (n : ℤ)
    (hn : n ≠ 0) (hn1 : n ≠ 1) (hnm : n ≠ -1) : f.coefficient n=0 := by
  have h := congrArg (fun f : SmoothCircleFunction => f.coefficient n) hf
  rw [coefficient_add,coefficient_differentiated,coefficient_differentiated,
    coefficient_zero_constant] at h
  have hi : (Complex.I*(n:ℂ))^3+Complex.I*(n:ℂ)=
      -Complex.I*(n:ℂ)*((n:ℂ)-1)*((n:ℂ)+1) := by
    calc
      _ = Complex.I^2*Complex.I*(n:ℂ)^3+Complex.I*(n:ℂ) := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [pow_one,← add_mul,hi] at h
  have hn' : (n:ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have h1 : (n:ℂ)-1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn1)
  have hm : (n:ℂ)+1 ≠ 0 := by
    intro hh; have he : (n:ℂ)=(-1:ℂ) := by linear_combination hh
    exact hnm (by exact_mod_cast he)
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hn') h1) hm)
end StronglyRationalVOA.SmoothCircleFunction
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma mobius_stress_vacuum (hc : A.toVertexAlgebra.C2Cofinite) (f : SmoothCircleFunction)
    (hf : (f.differentiated 3).add (f.differentiated 1)=SmoothCircleFunction.constant 0) :
    U.smoothSmear hc A.conformal_mem f.rapid_coefficients (U.smoothCoreVector A.vacuum)=0 := by
  apply Subtype.ext
  rw [smoothCoreVector,U.smoothSmear_coe,A.smearedMap_apply]
  change (∑' n : ℤ, f.coefficient n • (A.physicalMode A.conformalVector 2 n A.vacuum:Completion V))=0
  trans ∑' _ : ℤ, (0 : Completion V)
  · apply tsum_congr
    intro n
    by_cases hn : -1 ≤ n
    · have he : A.physicalMode A.conformalVector 2 n=A.virasoroMode n := by
        simp only [physicalMode,virasoroMode]
        congr 1
        omega
      rw [he,A.virasoro_vacuum n hn,Completion.coe_zero,smul_zero]
    · rw [f.coefficient_of_mobius_equation hf n (by omega) (by omega) (by omega),zero_smul]
  · simp
 

lemma diffeomorphism_mobius_vacuum_ray (hc : A.toVertexAlgebra.C2Cofinite)
    (M : SL(2,ℝ)) (F : SmoothCircleLift) (hF : CircleMobiusGeometry.Implements M F) :
    ∃ c : ℂ, U.diffeomorphismImplementer hc F (A.vacuum:Completion V)=c • (A.vacuum:Completion V) := by
  let E := U.diffeomorphismSmoothImplementer hc F
  let Ω := U.smoothCoreVector A.vacuum
  let y := E.symm Ω
  have h := U.diffeomorphism_stress_smooth hc F (fun _ => 1) contDiff_const
    (fun _ => rfl) (fun _ => zero_lt_one) y
  have htest : SmoothCircleFunction.ofRealPeriodic (fun _ => 1) (fun _ => rfl) contDiff_const=
      SmoothCircleFunction.constant 1 := by ext; rfl
  change U.smoothSmear hc A.conformal_mem
    (F.pushedTest (fun _ => 1) 1 contDiff_const (fun _ => rfl)).rapid_coefficients (E y)=
    E (U.smoothSmear hc A.conformal_mem
      (SmoothCircleFunction.ofRealPeriodic (fun _ => 1) (fun _ => rfl) contDiff_const).rapid_coefficients y)+
    F.anomaly (fun _ => 1) A.centralCharge • E y at h
  rw [CircleMobiusGeometry.anomaly_constant_zero M F hF,zero_smul,add_zero,htest] at h
  have hey : E y=Ω := E.apply_symm_apply Ω
  rw [hey,U.mobius_stress_vacuum hc _ (CircleMobiusGeometry.pushed_constant_mobius_equation M F hF)] at h
  have hz : U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.constant 1).rapid_coefficients y=0 :=
    E.injective (h.symm.trans (map_zero E).symm)
  have hg := U.smoothSmear_graph hc A.conformal_mem (SmoothCircleFunction.constant 1).rapid_coefficients y
  rw [hz] at hg
  obtain ⟨c,hc'⟩ := U.hamiltonian_kernel (U.stress_graph_le_hamiltonian hc hg)
  have hc0 : c ≠ 0 := by
    intro he
    rw [he,zero_smul] at hc'
    have hy0 : y=0 := Subtype.ext hc'
    have ho : Ω=0 := by rw [← hey,hy0,map_zero]
    have hv : (A.vacuum:Completion V)=0 := congrArg Subtype.val ho
    exact A.vacuum_ne_zero (Completion.coe_injective V (by simpa only [Completion.coe_zero] using hv))
  refine ⟨c⁻¹,?_⟩
  have he : (A.vacuum:Completion V)=c • U.diffeomorphismImplementer hc F (A.vacuum:Completion V) := by
    have H := congrArg (U.diffeomorphismImplementer hc F) hc'
    rw [map_smul] at H
    have HY : U.diffeomorphismImplementer hc F (y:Completion V)=(A.vacuum:Completion V) :=
      congrArg Subtype.val hey
    rwa [HY] at H
  calc
    _ = c⁻¹ • (c • U.diffeomorphismImplementer hc F (A.vacuum:Completion V)) := by
      rw [smul_smul,inv_mul_cancel₀ hc0,one_smul]
    _ = _ := congrArg (fun z : Completion V => c⁻¹ • z) he.symm
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
