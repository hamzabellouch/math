import OAI.RepresentationTheory.VertexAlgebra.MobiusGroup
import OAI.RepresentationTheory.VertexAlgebra.MobiusVacuum
import OAI.RepresentationTheory.VertexAlgebra.DiffeomorphismContinuity
import OAI.RepresentationTheory.VertexAlgebra.AlgebraCovariance

namespace OAI

noncomputable section
open UniformSpace Filter Set
open scoped Topology MatrixGroups
namespace StronglyRationalVOA
 
def phaseUnitary {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (c : ℂ) (hc : ‖c‖=1) : H ≃ₗᵢ[ℂ] H where
  toLinearEquiv := LinearEquiv.smulOfNeZero ℂ H c (by intro h; simp [h] at hc)
  norm_map' x := by simp only [LinearEquiv.smulOfNeZero_apply,norm_smul,hc,one_mul]
lemma phaseUnitary_apply {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (c : ℂ) (hc : ‖c‖=1) (x : H) : phaseUnitary c hc x=c • x := rfl
lemma projective_eq_of_phase {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (E F : H ≃ₗᵢ[ℂ] H) {c : ℂ} (hc : ‖c‖=1) (h : ∀ x,F x=c • E x) :
    (QuotientGroup.mk E : ProjectiveUnitaryGroup H)=QuotientGroup.mk F := by
  apply QuotientGroup.eq.mpr
  refine ⟨c,hc,?_⟩
  intro x
  change E.symm (F x)=c • x
  rw [h,map_smul,E.symm_apply_apply]
lemma projective_eq_vacuum_unique {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Ω : H) (hΩ : Ω ≠ 0) (E F : H ≃ₗᵢ[ℂ] H)
    (h : (QuotientGroup.mk E : ProjectiveUnitaryGroup H)=QuotientGroup.mk F)
    (he : E Ω=Ω) (hf : F Ω=Ω) : E=F := by
  obtain ⟨c,_,hc⟩ := QuotientGroup.eq.mp h
  have hEF (x : H) : F x=c • E x := by
    have H := congrArg E (hc x)
    change E (E.symm (F x))=E (c • x) at H
    simpa only [E.apply_symm_apply,map_smul] using H
  have hc1 : c=1 := by
    have hh := hEF Ω
    rw [he,hf] at hh
    exact (smul_left_injective ℂ hΩ) (hh.symm.trans (one_smul ℂ Ω).symm)
  ext x
  rw [hEF,hc1,one_smul]
end StronglyRationalVOA
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
include U in
lemma completion_vacuum_norm : ‖(A.vacuum:Completion V)‖=1 := by
  simpa only [Completion.norm_coe] using U.vacuum_norm
include U in
lemma completion_vacuum_ne_zero : (A.vacuum:Completion V) ≠ 0 := by
  intro h
  have hh := U.completion_vacuum_norm
  rw [h,norm_zero] at hh
  exact zero_ne_one hh
 
def mobiusVacuumPhase (hc : A.toVertexAlgebra.C2Cofinite) (F : CircleMobiusGeometry.lifts) : ℂ :=
  inner ℂ (A.vacuum:Completion V) (U.diffeomorphismImplementer hc F (A.vacuum:Completion V))
lemma mobiusVacuumPhase_spec (hc : A.toVertexAlgebra.C2Cofinite) (F : CircleMobiusGeometry.lifts) :
    U.diffeomorphismImplementer hc F (A.vacuum:Completion V)=
      U.mobiusVacuumPhase hc F • (A.vacuum:Completion V) := by
  obtain ⟨M,hM⟩ := F.property
  obtain ⟨c,he⟩ := U.diffeomorphism_mobius_vacuum_ray hc M F hM
  dsimp only [mobiusVacuumPhase]
  rw [he,inner_smul_right,inner_self_eq_norm_sq_to_K,U.completion_vacuum_norm]
  simp
lemma mobiusVacuumPhase_norm (hc : A.toVertexAlgebra.C2Cofinite) (F : CircleMobiusGeometry.lifts) :
    ‖U.mobiusVacuumPhase hc F‖=1 := by
  have h := congrArg norm (U.mobiusVacuumPhase_spec hc F)
  rw [(U.diffeomorphismImplementer hc F).norm_map,norm_smul,U.completion_vacuum_norm,mul_one] at h
  exact h.symm
lemma mobiusVacuumPhase_ne_zero (hc : A.toVertexAlgebra.C2Cofinite) (F : CircleMobiusGeometry.lifts) :
    U.mobiusVacuumPhase hc F ≠ 0 := by
  intro h
  have he := U.mobiusVacuumPhase_norm hc F
  rw [h,norm_zero] at he
  exact zero_ne_one he
 
def mobiusLiftUnitary (hc : A.toVertexAlgebra.C2Cofinite) (F : CircleMobiusGeometry.lifts) :
    Completion V ≃ₗᵢ[ℂ] Completion V :=
  (U.diffeomorphismImplementer hc F).trans
    (phaseUnitary (U.mobiusVacuumPhase hc F)⁻¹ (by rw [norm_inv,U.mobiusVacuumPhase_norm,inv_one]))
lemma mobiusLiftUnitary_apply (hc : A.toVertexAlgebra.C2Cofinite) (F : CircleMobiusGeometry.lifts)
    (x : Completion V) : U.mobiusLiftUnitary hc F x=
      (U.mobiusVacuumPhase hc F)⁻¹ • U.diffeomorphismImplementer hc F x := rfl
lemma mobiusLiftUnitary_vacuum (hc : A.toVertexAlgebra.C2Cofinite) (F : CircleMobiusGeometry.lifts) :
    U.mobiusLiftUnitary hc F (A.vacuum:Completion V)=(A.vacuum:Completion V) := by
  rw [U.mobiusLiftUnitary_apply,U.mobiusVacuumPhase_spec,smul_smul,
    inv_mul_cancel₀ (U.mobiusVacuumPhase_ne_zero hc F),one_smul]
lemma mobiusLiftUnitary_projective (hc : A.toVertexAlgebra.C2Cofinite) (F : CircleMobiusGeometry.lifts) :
    (QuotientGroup.mk (U.mobiusLiftUnitary hc F) : ProjectiveUnitaryGroup (Completion V))=
      U.liftProjectiveRepresentation hc F := by
  exact (projective_eq_of_phase _ _
    (by rw [norm_inv,U.mobiusVacuumPhase_norm,inv_one]) (U.mobiusLiftUnitary_apply hc F)).symm
lemma mobiusLiftUnitary_mul (hc : A.toVertexAlgebra.C2Cofinite) (F G : CircleMobiusGeometry.lifts) :
    U.mobiusLiftUnitary hc (F*G)=U.mobiusLiftUnitary hc F*U.mobiusLiftUnitary hc G := by
  apply projective_eq_vacuum_unique (A.vacuum:Completion V) U.completion_vacuum_ne_zero
  · rw [QuotientGroup.mk_mul,U.mobiusLiftUnitary_projective,U.mobiusLiftUnitary_projective,
      U.mobiusLiftUnitary_projective]
    exact map_mul (U.liftProjectiveRepresentation hc) (F:SmoothCircleLift) (G:SmoothCircleLift)
  · exact U.mobiusLiftUnitary_vacuum hc (F*G)
  · change U.mobiusLiftUnitary hc F (U.mobiusLiftUnitary hc G (A.vacuum:Completion V))=_
    rw [U.mobiusLiftUnitary_vacuum,U.mobiusLiftUnitary_vacuum]
def mobiusLiftRepresentation (hc : A.toVertexAlgebra.C2Cofinite) :
    CircleMobiusGeometry.lifts →* (Completion V ≃ₗᵢ[ℂ] Completion V) :=
  MonoidHom.mk' (U.mobiusLiftUnitary hc) (U.mobiusLiftUnitary_mul hc)
lemma mobiusLiftRepresentation_kernel (hc : A.toVertexAlgebra.C2Cofinite)
    (F : CircleMobiusGeometry.lifts)
    (hF : F ∈ (SmoothCircleLift.circleAction.comp CircleMobiusGeometry.lifts.subtype).ker) :
    U.mobiusLiftRepresentation hc F=1 := by
  apply projective_eq_vacuum_unique (A.vacuum:Completion V) U.completion_vacuum_ne_zero
  · change (QuotientGroup.mk (U.mobiusLiftUnitary hc F) : ProjectiveUnitaryGroup (Completion V))=1
    rw [U.mobiusLiftUnitary_projective]
    have h : (QuotientGroup.mk (F:SmoothCircleLift) : SmoothCircleDiffeomorphism)=1 :=
      (QuotientGroup.eq_one_iff _).mpr hF
    exact (congrArg (U.diffeomorphismProjectiveRepresentation hc) h).trans (map_one _)
  · exact U.mobiusLiftUnitary_vacuum hc F
  · rfl
 

def mobiusRepresentation (hc : A.toVertexAlgebra.C2Cofinite) :
    CircleMobiusGeometry.Group →* (Completion V ≃ₗᵢ[ℂ] Completion V) :=
  QuotientGroup.lift (SmoothCircleLift.circleAction.comp CircleMobiusGeometry.lifts.subtype).ker
    (U.mobiusLiftRepresentation hc) (by intro F hF; exact U.mobiusLiftRepresentation_kernel hc F hF)
lemma mobiusRepresentation_vacuum (hc : A.toVertexAlgebra.C2Cofinite) (F : CircleMobiusGeometry.Group) :
    U.mobiusRepresentation hc F (A.vacuum:Completion V)=(A.vacuum:Completion V) := by
  induction F using QuotientGroup.induction_on with
  | H F => exact U.mobiusLiftUnitary_vacuum hc F
lemma mobiusRepresentation_projective (hc : A.toVertexAlgebra.C2Cofinite) (F : CircleMobiusGeometry.Group) :
    (QuotientGroup.mk (U.mobiusRepresentation hc F) : ProjectiveUnitaryGroup (Completion V))=
      U.diffeomorphismProjectiveRepresentation hc (CircleMobiusGeometry.inclusion F) := by
  induction F using QuotientGroup.induction_on with
  | H F => exact U.mobiusLiftUnitary_projective hc F
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
