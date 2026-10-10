import OAI.RepresentationTheory.VertexAlgebra.MobiusRepresentation

namespace OAI

noncomputable section
open UniformSpace Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleLift
lemma rotation_angularVelocity (s t : ℝ) :
    (rotation s).unitLift.angularVelocity t=
      SmoothCircleFunction.constant ((s*deriv Real.smoothTransition t:ℝ):ℂ) := by
  ext x
  let y := (rotation s).unitLift.inverse t (x/(2*Real.pi))
  change ((2*Real.pi*(deriv Real.smoothTransition t*
    (((2*Real.pi*y+s)/(2*Real.pi))-y)):ℝ):ℂ)=((s*deriv Real.smoothTransition t:ℝ):ℂ)
  congr 1
  field_simp [Real.pi_ne_zero]
  ring
end StronglyRationalVOA.SmoothCircleLift
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma rotationPropagatorDerivative (hc : A.toVertexAlgebra.C2Cofinite) (s t : ℝ)
    (x : U.smoothEnergySpace) :
    U.stressPropagatorDerivative hc (SmoothCircleLift.rotation s).unitLift.angularStressPath t x=
      (Complex.I*(s*deriv Real.smoothTransition t:ℝ)) •
      (U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.constant 1).rapid_coefficients
        (U.stressPropagatorSmooth hc (SmoothCircleLift.rotation s).unitLift.angularStressPath t x):Completion V) := by
  rw [U.stressPropagatorDerivative_smoothSmear]
  change Complex.I • (U.smoothSmear hc A.conformal_mem
    ((SmoothCircleLift.rotation s).unitLift.angularVelocity t).rapid_coefficients _ : Completion V)=_
  rw [SmoothCircleLift.rotation_angularVelocity,U.smoothSmear_constant]
  simp only [LinearMap.smul_apply,Submodule.coe_smul,smul_smul]
 

lemma diffeomorphismImplementer_rotation (hc : A.toVertexAlgebra.C2Cofinite) (s : ℝ)
    (x : Completion V) :
    U.diffeomorphismImplementer hc (SmoothCircleLift.rotation s) x=U.rotation s x := by
  let f := (SmoothCircleLift.rotation s).unitLift.angularStressPath
  let T := U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.constant 1).rapid_coefficients
  let τ : ℝ → ℝ := fun t => s*Real.smoothTransition t
  have hτ (t : ℝ) : HasDerivAt τ (s*deriv Real.smoothTransition t) t :=
    (((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp) t).hasDerivAt).const_mul s
  have hp (z : U.smoothEnergySpace) (d : ℕ) (v : A.grade d) :
      inner ℂ (U.stressPropagator hc f 1 z) (U.rotation s (v.val:Completion V))=
        inner ℂ (z:Completion V) (v.val:Completion V) := by
    let a : ℝ → ℂ := fun t => Complex.exp ((τ t:ℂ)*(d:ℂ)*Complex.I)
    have ha (t : ℝ) : HasDerivAt a
        (a t*((s*deriv Real.smoothTransition t:ℝ):ℂ)*(d:ℂ)*Complex.I) t := by
      convert (((hτ t).ofReal_comp.mul_const (d:ℂ)).mul_const Complex.I).cexp using 1
      first | rfl | ring
    have hg : ((v.val:Completion V),(d:ℂ) • (v.val:Completion V)) ∈ U.conformalHamiltonian.graph := by
      exact U.conformalHamiltonian.mem_graph_iff.mpr
        ⟨⟨(v.val:Completion V),U.coe_mem_energyOperator (fun d => d) v.val⟩,rfl,U.energyOperator_grade _ v⟩
    have hd (t : ℝ) : HasDerivAt (fun t =>
        inner ℂ (U.stressPropagator hc f t z) (a t • (v.val:Completion V))) 0 t := by
      have H := (U.stressPropagator_derivative hc f t z).inner ℂ ((ha t).smul_const (v.val:Completion V))
      have he := SymmetricOperator.formalAdjoint_graph_pairing
        (SymmetricOperator.selfAdjoint_formal (U.energyOperator_selfAdjoint (fun d => d)))
        (U.stress_graph_le_hamiltonian hc (U.smoothSmear_graph hc A.conformal_mem
          (SmoothCircleFunction.constant 1).rapid_coefficients (U.stressPropagatorSmooth hc f t z))) hg
      change inner ℂ (T (U.stressPropagatorSmooth hc f t z):Completion V) (v.val:Completion V)=
        inner ℂ (U.stressPropagator hc f t z) ((d:ℂ) • (v.val:Completion V)) at he
      rw [inner_smul_right] at he
      rw [U.rotationPropagatorDerivative hc s t z,inner_smul_left,inner_smul_right,
        inner_smul_right,map_mul,Complex.conj_I,Complex.conj_ofReal] at H
      change HasDerivAt _
        ((a t*((s*deriv Real.smoothTransition t:ℝ):ℂ)*(d:ℂ)*Complex.I)*
          inner ℂ (U.stressPropagator hc f t z) (v.val:Completion V)+
          ((-Complex.I)*((s*deriv Real.smoothTransition t:ℝ):ℂ)) *
          (a t*inner ℂ (T (U.stressPropagatorSmooth hc f t z):Completion V) (v.val:Completion V))) t at H
      rw [he] at H
      convert H using 1
      first | rfl | ring
    have h := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
      (fun t => (hd t).deriv) 1 0
    have ha0 : a 0=1 := by simp [a,τ]
    have ha1 : a 1=Complex.exp ((s*d:ℝ)*Complex.I) := by simp [a,τ]
    rw [ha0,one_smul,U.stressPropagator_zero,one_apply_eq_self,ha1] at h
    rwa [U.rotation_grade s v]
  have hpf (z : U.smoothEnergySpace) (v : V) :
      inner ℂ (U.stressPropagator hc f 1 z) (U.rotation s (v:Completion V))=
        inner ℂ (z:Completion V) (v:Completion V) := by
    apply A.homogeneous_induction (P := fun v =>
      inner ℂ (U.stressPropagator hc f 1 z) (U.rotation s (v:Completion V))=
        inner ℂ (z:Completion V) (v:Completion V))
    · change inner ℂ _ (U.rotation s (0:Completion V))=inner ℂ _ 0
      simp only [map_zero,inner_zero_right]
    · intro d v hv; exact hp z d ⟨v,hv⟩
    · intro u v hu hv
      simp only [Completion.coe_add,map_add,inner_add_right,hu,hv]
  have hall (z y : Completion V) :
      inner ℂ (U.stressPropagator hc f 1 z) (U.rotation s y)=inner ℂ z y := by
    refine U.smoothEnergySpace_dense.denseRange_val.induction_on z ?_ ?_
    · exact isClosed_eq ((U.stressPropagator hc f 1).continuous.inner continuous_const)
        (continuous_id.inner continuous_const)
    · intro z
      refine Completion.denseRange_coe.induction_on y ?_ ?_
      · exact isClosed_eq (continuous_const.inner (U.rotation s).continuous)
          (continuous_const.inner continuous_id)
      · exact hpf z
  apply ext_inner_right ℂ
  intro y
  have hy : U.rotation s (U.rotation (-s) y)=y := by
    change (U.rotation s*U.rotation (-s)) y=y
    rw [← U.rotation_add,add_neg_cancel,U.rotation_zero,one_apply_eq_self]
  rw [← hy]
  change inner ℂ (U.stressPropagator hc f 1 x) (U.rotation s (U.rotation (-s) y))=_
  rw [hall,U.rotation_inner]
lemma mobiusRepresentation_rotation (hc : A.toVertexAlgebra.C2Cofinite) (s : ℝ) (x : Completion V) :
    U.mobiusRepresentation hc (QuotientGroup.mk (CircleMobiusGeometry.rotation s)) x=U.rotation s x := by
  change U.mobiusLiftUnitary hc (CircleMobiusGeometry.rotation s) x=_
  rw [U.mobiusLiftUnitary_apply]
  have hphase : U.mobiusVacuumPhase hc (CircleMobiusGeometry.rotation s)=1 := by
    dsimp only [mobiusVacuumPhase,CircleMobiusGeometry.rotation]
    rw [U.diffeomorphismImplementer_rotation,U.rotation_vacuum,inner_self_eq_norm_sq_to_K,
      U.completion_vacuum_norm]
    simp
  rw [hphase,inv_one,one_smul]
  exact U.diffeomorphismImplementer_rotation hc s x
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
