import OAI.RepresentationTheory.VertexAlgebra.ModuleCreationTotality
import OAI.RepresentationTheory.VertexAlgebra.ModuleIntegrationUniqueness

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule.UnitaryStructure
open UniformSpace
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {M : A.GradingRestrictedModule W} (R : M.UnitaryStructure U)

 

def HasLocalCreationCovers (hc : A.toVertexAlgebra.C2Cofinite) : Prop :=
  ∀ I : ProperCircleArc, ∀ a : W, ∀ z : ℂ, a ∈ M.grade z →
    ∀ f : SmoothCircleFunction, tsupport f.onCircle ⊆ I.complement.carrier →
      ∃ (T : R.LocalGraphIntertwiner hc I) (x : Completion V),
        T.val x = M.creationVacuumSmear a f

 

theorem totalGraphIntertwiners_of_localCreationCovers
    (hc : A.toVertexAlgebra.C2Cofinite) (hCover : R.HasLocalCreationCovers hc) :
    R.HasTotalLocalGraphIntertwiners hc := by
  intro I
  let S := BoundedIntertwiner.core (R.localGraphIntertwinerMap hc I)
  have hsub : Submodule.span ℂ (M.localVacuumCreations I.complement) ≤
      LinearMap.range S := by
    apply Submodule.span_le.mpr
    rintro y ⟨a,z,ha,f,hf,rfl⟩
    obtain ⟨T,x,hx⟩ := hCover I a z ha f hf
    refine ⟨Finsupp.single T x, ?_⟩
    change BoundedIntertwiner.core (R.localGraphIntertwinerMap hc I)
      (Finsupp.single T x) = M.creationVacuumSmear a f
    rw [BoundedIntertwiner.core_single]
    exact hx
  have hd : (LinearMap.range S).topologicalClosure = ⊤ := by
    apply top_unique
    rw [← R.localVacuumCreations_total I.complement]
    exact Submodule.topologicalClosure_mono hsub
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hd

 

theorem localIntegrationConclusion_of_localCreationCovers
    (hc : A.toVertexAlgebra.C2Cofinite) (hCover : R.HasLocalCreationCovers hc) :
    R.LocalIntegrationConclusion hc :=
  R.localIntegrationConclusion_of_totalGraphIntertwiners hc
    (R.totalGraphIntertwiners_of_localCreationCovers hc hCover)

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule.UnitaryStructure

end

end OAI
