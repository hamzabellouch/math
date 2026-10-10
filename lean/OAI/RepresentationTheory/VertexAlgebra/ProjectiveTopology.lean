import OAI.RepresentationTheory.VertexAlgebra.SmoothTopology

namespace OAI

noncomputable section
open UniformSpace Filter Set
open scoped Topology
namespace StronglyRationalVOA

 

instance unitaryStrongTopology (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    TopologicalSpace (H ≃ₗᵢ[ℂ] H) :=
  TopologicalSpace.induced (fun E : H ≃ₗᵢ[ℂ] H => (E : H → H)) inferInstance

lemma unitaryStrong_isInducing (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Topology.IsInducing (fun E : H ≃ₗᵢ[ℂ] H => (E : H → H)) := ⟨rfl⟩

lemma unitaryStrong_continuous_apply {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x : H) : Continuous (fun E : H ≃ₗᵢ[ℂ] H => E x) :=
  (continuous_apply x).comp (unitaryStrong_isInducing H).continuous

lemma unitaryStrong_continuous_mul_right {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (E : H ≃ₗᵢ[ℂ] H) : Continuous (fun F : H ≃ₗᵢ[ℂ] H => F*E) := by
  apply (unitaryStrong_isInducing H).continuous_iff.mpr
  apply continuous_pi
  intro x
  exact unitaryStrong_continuous_apply (E x)

 
lemma projectiveStrong_continuous_mul_right {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (E : ProjectiveUnitaryGroup H) : Continuous (fun F : ProjectiveUnitaryGroup H => F*E) := by
  induction E using QuotientGroup.induction_on with
  | H E =>
    apply (QuotientGroup.isQuotientMap_mk (scalarPhaseSubgroup H)).continuous_iff.mpr
    change Continuous (fun F : H ≃ₗᵢ[ℂ] H => QuotientGroup.mk F*QuotientGroup.mk E)
    simp only [← QuotientGroup.mk_mul]
    exact (QuotientGroup.isQuotientMap_mk (scalarPhaseSubgroup H)).continuous.comp
      (unitaryStrong_continuous_mul_right E)

 

instance : TopologicalSpace SmoothCircleDiffeomorphism := inferInstanceAs
  (TopologicalSpace (SmoothCircleLift ⧸ SmoothCircleLift.circleAction.ker))
end StronglyRationalVOA

end

end OAI
