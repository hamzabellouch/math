import OAI.RepresentationTheory.VertexAlgebra.StrongContinuity
import OAI.RepresentationTheory.VertexAlgebra.ProjectiveTopology

namespace OAI

noncomputable section
open UniformSpace Filter Set
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma liftProjectiveRepresentation_continuousAt_one (hc : A.toVertexAlgebra.C2Cofinite) :
    ContinuousAt (U.liftProjectiveRepresentation hc) 1 := by
  have hi : ContinuousAt (U.diffeomorphismImplementer hc) 1 := by
    apply (unitaryStrong_isInducing (Completion V)).continuousAt_iff.mpr
    exact continuousAt_pi.mpr (fun x => U.diffeomorphismImplementer_continuousAt_one hc x)
  exact (QuotientGroup.isQuotientMap_mk (scalarPhaseSubgroup (Completion V))).continuous.continuousAt.comp hi

 

theorem liftProjectiveRepresentation_continuous (hc : A.toVertexAlgebra.C2Cofinite) :
    Continuous (U.liftProjectiveRepresentation hc) := by
  apply continuous_iff_continuousAt.mpr
  intro F
  have hnear : Tendsto (fun G : SmoothCircleLift => G*F⁻¹) (𝓝 F) (𝓝 1) := by
    simpa only [mul_inv_cancel] using (SmoothCircleLift.continuous_mul_right F⁻¹).tendsto F
  have h := (U.liftProjectiveRepresentation_continuousAt_one hc).tendsto.comp hnear
  have hpost := (projectiveStrong_continuous_mul_right (U.liftProjectiveRepresentation hc F)).tendsto
    (U.liftProjectiveRepresentation hc 1)
  have H := hpost.comp h
  change Tendsto (U.liftProjectiveRepresentation hc) (𝓝 F) (𝓝 (U.liftProjectiveRepresentation hc F))
  simpa only [Function.comp_def,map_mul,map_inv,map_one,one_mul,mul_assoc,inv_mul_cancel,mul_one] using H

 

theorem diffeomorphismProjectiveRepresentation_continuous (hc : A.toVertexAlgebra.C2Cofinite) :
    Continuous (U.diffeomorphismProjectiveRepresentation hc) := by
  apply (QuotientGroup.isQuotientMap_mk SmoothCircleLift.circleAction.ker).continuous_iff.mpr
  exact U.liftProjectiveRepresentation_continuous hc
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
