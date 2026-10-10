import OAI.RepresentationTheory.VertexAlgebra.MobiusRepresentation

namespace OAI

noncomputable section
open UniformSpace Filter Set
open scoped Topology
namespace StronglyRationalVOA.CircleMobiusGeometry
lemma continuous_mul_right (F : lifts) : Continuous (fun G : lifts => G*F) := by
  apply Continuous.subtype_mk
  exact (SmoothCircleLift.continuous_mul_right (F:SmoothCircleLift)).comp continuous_subtype_val
end StronglyRationalVOA.CircleMobiusGeometry
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma mobiusVacuumPhase_continuousAt_one (hc : A.toVertexAlgebra.C2Cofinite) :
    ContinuousAt (U.mobiusVacuumPhase hc) 1 := by
  apply ContinuousAt.inner continuousAt_const
  have hval : Tendsto (fun F : CircleMobiusGeometry.lifts => (F:SmoothCircleLift))
      (𝓝 1) (𝓝 (1:SmoothCircleLift)) := continuous_subtype_val.tendsto (1:CircleMobiusGeometry.lifts)
  exact (U.diffeomorphismImplementer_continuousAt_one hc (A.vacuum:Completion V)).tendsto.comp hval
lemma mobiusLiftRepresentation_continuousAt_one (hc : A.toVertexAlgebra.C2Cofinite) :
    ContinuousAt (U.mobiusLiftRepresentation hc) 1 := by
  apply (unitaryStrong_isInducing (Completion V)).continuousAt_iff.mpr
  apply continuousAt_pi.mpr
  intro x
  change ContinuousAt (fun F : CircleMobiusGeometry.lifts => U.mobiusLiftUnitary hc F x) 1
  simp only [U.mobiusLiftUnitary_apply]
  have hval : Tendsto (fun F : CircleMobiusGeometry.lifts => (F:SmoothCircleLift))
      (𝓝 1) (𝓝 (1:SmoothCircleLift)) := continuous_subtype_val.tendsto (1:CircleMobiusGeometry.lifts)
  exact ((U.mobiusVacuumPhase_continuousAt_one hc).inv₀ (U.mobiusVacuumPhase_ne_zero hc 1)).smul
    ((U.diffeomorphismImplementer_continuousAt_one hc x).tendsto.comp hval)
lemma mobiusLiftRepresentation_continuous (hc : A.toVertexAlgebra.C2Cofinite) :
    Continuous (U.mobiusLiftRepresentation hc) := by
  apply continuous_iff_continuousAt.mpr
  intro F
  have hnear : Tendsto (fun G : CircleMobiusGeometry.lifts => G*F⁻¹) (𝓝 F) (𝓝 1) := by
    simpa only [mul_inv_cancel] using (CircleMobiusGeometry.continuous_mul_right F⁻¹).tendsto F
  have h := (U.mobiusLiftRepresentation_continuousAt_one hc).tendsto.comp hnear
  have hpost := (unitaryStrong_continuous_mul_right (U.mobiusLiftRepresentation hc F)).tendsto
    (U.mobiusLiftRepresentation hc 1)
  have H := hpost.comp h
  change Tendsto (U.mobiusLiftRepresentation hc) (𝓝 F) (𝓝 (U.mobiusLiftRepresentation hc F))
  simpa only [Function.comp_def,map_mul,map_inv,map_one,one_mul,mul_assoc,inv_mul_cancel,mul_one] using H
 
theorem mobiusRepresentation_continuous (hc : A.toVertexAlgebra.C2Cofinite) :
    Continuous (U.mobiusRepresentation hc) := by
  apply (QuotientGroup.isQuotientMap_mk
    (SmoothCircleLift.circleAction.comp CircleMobiusGeometry.lifts.subtype).ker).continuous_iff.mpr
  exact U.mobiusLiftRepresentation_continuous hc
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
