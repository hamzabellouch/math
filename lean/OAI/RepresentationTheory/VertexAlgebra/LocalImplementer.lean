import OAI.RepresentationTheory.VertexAlgebra.AlgebraCovariance

namespace OAI

noncomputable section
open UniformSpace Set
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

lemma stressPropagator_commutes_of_graph (hc : A.toVertexAlgebra.C2Cofinite)
    (f : StressPath) (Q : Completion V →L[ℂ] Completion V)
    (hQ : ∀ t x y, (x,y) ∈ (U.closedSmearedOperator hc A.conformalVector 2
      (f.coefficients t) (f.rapid t)).graph →
      (Q x,Q y) ∈ (U.closedSmearedOperator hc A.conformalVector 2
        (f.coefficients t) (f.rapid t)).graph) (t : ℝ) :
    Q*U.stressPropagator hc f t=U.stressPropagator hc f t*Q := by
  have hp (x y : U.smoothEnergySpace) :
      inner ℂ (U.stressPropagator hc f t x) (Q (U.stressPropagator hc f t y))=
      inner ℂ (x:Completion V) (Q y) := by
    have hd (s : ℝ) : HasDerivAt (fun s =>
        inner ℂ (U.stressPropagator hc f s x) (Q (U.stressPropagator hc f s y))) 0 s := by
      have H := (U.stressPropagator_derivative hc f s x).inner ℂ
        ((Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (U.stressPropagator_derivative hc f s y))
      have he := SymmetricOperator.formalAdjoint_graph_pairing
        (SymmetricOperator.selfAdjoint_formal
          (U.stress_closedSmearedOperator_selfAdjoint hc (f.rapid s) (f.real s)))
        (U.smoothSmear_graph hc A.conformal_mem (f.rapid s) (U.stressPropagatorSmooth hc f s x))
        (hQ s _ _ (U.smoothSmear_graph hc A.conformal_mem (f.rapid s)
          (U.stressPropagatorSmooth hc f s y)))
      have hre (v : Completion V) : (Q.restrictScalars ℝ) v=Q v := rfl
      simp only [Function.comp_apply,hre] at H
      change inner ℂ
        (U.smoothSmear hc A.conformal_mem (f.rapid s) (U.stressPropagatorSmooth hc f s x) : Completion V)
        (Q (U.stressPropagator hc f s y))=
        inner ℂ (U.stressPropagator hc f s x)
        (Q (U.smoothSmear hc A.conformal_mem (f.rapid s) (U.stressPropagatorSmooth hc f s y) : Completion V)) at he
      rw [U.stressPropagatorDerivative_smoothSmear hc f s x,
        U.stressPropagatorDerivative_smoothSmear hc f s y,
        map_smul,inner_smul_left,inner_smul_right,Complex.conj_I,he] at H
      convert H using 1
      first | rfl | ring
    have he := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
      (fun s => (hd s).deriv) t 0
    simpa only [U.stressPropagator_zero,one_apply_eq_self] using he
  have hall (x y : Completion V) :
      inner ℂ (U.stressPropagator hc f t x) (Q (U.stressPropagator hc f t y))=
      inner ℂ x (Q y) := by
    refine U.smoothEnergySpace_dense.denseRange_val.induction_on x ?_ ?_
    · exact isClosed_eq ((U.stressPropagator hc f t).continuous.inner continuous_const)
        (continuous_id.inner continuous_const)
    · intro x
      refine U.smoothEnergySpace_dense.denseRange_val.induction_on y ?_ ?_
      · exact isClosed_eq (continuous_const.inner (Q.continuous.comp (U.stressPropagator hc f t).continuous))
          (continuous_const.inner Q.continuous)
      · intro y; exact hp x y
  ext y
  apply ext_inner_left ℂ
  intro z
  obtain ⟨x,rfl⟩ := (U.stressPropagatorEquiv hc f t).surjective z
  exact (hall x y).trans ((U.stressPropagatorEquiv hc f t).inner_map_map x (Q y)).symm
 
lemma angularStressPath_local_action (hc : A.toVertexAlgebra.C2Cofinite)
    (φ : PositiveCircleGeometry.SmoothLift)
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O)
    (hv : ∀ t, tsupport (φ.angularVelocity t).onCircle ⊆ Oᶜ)
    {Q : Completion V →L[ℂ] Completion V} (hQ : Q ∈ U.localAlgebra hc O)
    (t : ℝ) : Q*U.stressPropagator hc φ.angularStressPath t=
      U.stressPropagator hc φ.angularStressPath t*Q := by
  apply U.stressPropagator_commutes_of_graph hc φ.angularStressPath Q
  intro s x y hxy
  let T : U.PrimaryTestField :=
    ⟨A.conformalVector,2,A.conformal_mem,A.conformal_quasiPrimary,U.stress_hermitian,
      φ.angularVelocity s,φ.angularVelocity_real s,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩
  apply T.commutant_preserves_graph hc (hv s) _ hxy
  apply U.primaryAlgebra_locality hc disjoint_compl_right
  rwa [U.localAlgebra_eq_primaryAlgebra hc hO] at hQ
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.PositiveCircleGeometry.SmoothLift
variable (φ : SmoothLift)
lemma velocity_zero_of_fixed (t x : ℝ) (hx : φ x=x) : φ.velocity t x=0 := by
  have hi : φ.interpolate t x=x := by dsimp [interpolate]; rw [hx]; ring
  have hinv : φ.inverse t x=x := by simpa only [hi] using φ.inverse_interpolate t x
  simp only [velocity,hinv,hx,sub_self,mul_zero]
end StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

namespace StronglyRationalVOA.SmoothCircleLift
lemma angularVelocity_zero_of_fixed (F : SmoothCircleLift) (t x : ℝ) (hx : F x=x) :
    F.unitLift.angularVelocity t x=0 := by
  have hu : F.unitLift (x/(2*Real.pi))=x/(2*Real.pi) := by
    change F (2*Real.pi*(x/(2*Real.pi)))/(2*Real.pi)=_
    rw [mul_div_cancel₀ _ (by positivity : (2*Real.pi:ℝ)≠0),hx]
  change ((2*Real.pi*F.unitLift.velocity t (x/(2*Real.pi)) : ℝ):ℂ)=0
  rw [F.unitLift.velocity_zero_of_fixed t _ hu,mul_zero,Complex.ofReal_zero]
lemma angularVelocity_support_of_fixed (F : SmoothCircleLift)
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O)
    (hfixed : ∀ x : ℝ, (x : AddCircle (2*Real.pi)) ∈ O → F x=x) (t : ℝ) :
    tsupport (F.unitLift.angularVelocity t).onCircle ⊆ Oᶜ := by
  apply closure_minimal _ hO.isClosed_compl
  intro z hz hmem
  obtain ⟨x,rfl⟩ := QuotientAddGroup.mk_surjective z
  exact hz (F.angularVelocity_zero_of_fixed t x (hfixed x hmem))
end StronglyRationalVOA.SmoothCircleLift

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma diffeomorphism_local_action_of_fixed_lift (hc : A.toVertexAlgebra.C2Cofinite)
    (F : SmoothCircleLift) {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O)
    (hfixed : ∀ x : ℝ, (x : AddCircle (2*Real.pi)) ∈ O → F x=x)
    {Q : Completion V →L[ℂ] Completion V} (hQ : Q ∈ U.localAlgebra hc O) :
    (U.diffeomorphismImplementer hc F).conjStarAlgEquiv Q=Q := by
  have he := U.angularStressPath_local_action hc F.unitLift hO
    (F.angularVelocity_support_of_fixed hO hfixed) hQ 1
  have hx (x : Completion V) := congrArg (fun B : Completion V →L[ℂ] Completion V => B x) he
  ext x
  exact ((hx ((U.diffeomorphismImplementer hc F).symm x)).symm.trans
    (congrArg Q ((U.diffeomorphismImplementer hc F).apply_symm_apply x)))
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
