import OAI.RepresentationTheory.VertexAlgebra.SmoothTopology

namespace OAI

noncomputable section
open UniformSpace Filter Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

lemma identity_angularVelocity (t : ℝ) :
    identity.angularVelocity t=SmoothCircleFunction.constant 0 := by
  ext x
  change ((2*Real.pi*(deriv Real.smoothTransition t *
    (identity (identity.inverse t (x/(2*Real.pi)))-identity.inverse t (x/(2*Real.pi)))) : ℝ) : ℂ)=0
  simp
lemma identity_path_coefficients (t : ℝ) (n : ℤ) :
    identity.angularStressPath.coefficients t n=0 := by
  change (identity.angularVelocity t).coefficient n=0
  rw [identity_angularVelocity,SmoothCircleFunction.coefficient_zero_constant]
end StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

 

theorem diffeomorphismImplementer_continuousAt_one
    (hc : A.toVertexAlgebra.C2Cofinite) (x : Completion V) :
    ContinuousAt (fun F : SmoothCircleLift => U.diffeomorphismImplementer hc F x) 1 := by
  let e : SmoothCircleLift → ℝ := fun F => F.unitLift.identityError
  have he : Continuous e := PositiveCircleGeometry.SmoothLift.continuous_identityError.comp
    SmoothCircleLift.continuous_unitLift
  have he0 : e 1=0 := by simp [e]
  have he' : Tendsto e (𝓝 1) (𝓝 0) := he0 ▸ he.continuousAt
  obtain ⟨C,hC,hbound⟩ := PositiveCircleGeometry.SmoothLift.angularStressPath_small_near_identity
  have hε : Tendsto (fun F => C*e F) (𝓝 1) (𝓝 0) := by simpa using he'.const_mul C
  have hd : ∀ᶠ F : SmoothCircleLift in 𝓝 1, ∀ t ∈ uIcc (0:ℝ) 1,
      coefficientSeminorm (fun k => F.unitLift.angularStressPath.coefficients t k-
        PositiveCircleGeometry.SmoothLift.identity.angularStressPath.coefficients t k) 2 ≤ C*e F := by
    have hn : ∀ᶠ F in 𝓝 (1 : SmoothCircleLift), e F < 1/2 :=
      he'.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))
    filter_upwards [hn] with F hF
    intro t _
    simp only [PositiveCircleGeometry.SmoothLift.identity_path_coefficients,sub_zero]
    exact hbound F.unitLift (e F) F.unitLift.identityError_nonneg hF.le
      F.unitLift.identityError_controls_zero F.unitLift.identityError_controls_one
      F.unitLift.identityError_controls_higher t
  have H := U.stressPropagator_path_tendsto_fixed hc
    PositiveCircleGeometry.SmoothLift.identity.angularStressPath
    (fun F : SmoothCircleLift => F.unitLift.angularStressPath) 1 (fun F => C*e F)
    (fun F => mul_nonneg hC.le F.unitLift.identityError_nonneg) hε hd x
  change Tendsto (fun F : SmoothCircleLift => U.stressPropagator hc F.unitLift.angularStressPath 1 x)
    (𝓝 1) (𝓝 (U.stressPropagator hc (1 : SmoothCircleLift).unitLift.angularStressPath 1 x))
  rw [SmoothCircleLift.unitLift_one]
  exact H
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
