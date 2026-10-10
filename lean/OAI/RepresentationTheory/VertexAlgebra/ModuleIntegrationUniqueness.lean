import OAI.RepresentationTheory.VertexAlgebra.ModuleGraphIntertwiners
import OAI.RepresentationTheory.VertexAlgebra.GeneratedNormalUniqueness

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule.UnitaryStructure
open UniformSpace
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {M : A.GradingRestrictedModule W} (R : M.UnitaryStructure U)

theorem compatibleClosedFieldAction_unique (hc : A.toVertexAlgebra.C2Cofinite)
    (π ρ : R.LocalActionFamily hc)
    (hπ : R.IsCompatibleClosedFieldAction hc π)
    (hρ : R.IsCompatibleClosedFieldAction hc ρ) : π = ρ := by
  funext I
  apply LocalOperatorAlgebra.normal_ext_generated (U.localGraphData hc I.carrier)
    (π I) (ρ I) (hπ.1 I) (hρ.1 I)
  intro x hx
  obtain ⟨a,d,ha,f,hf,i,j,rfl⟩ := hx
  exact (hπ.2.2 I a d ha f hf i j).trans (hρ.2.2 I a d ha f hf i j).symm

 
theorem localIntegrationConclusion_of_totalGraphIntertwiners
    (hc : A.toVertexAlgebra.C2Cofinite) (hTotal : R.HasTotalLocalGraphIntertwiners hc) :
    R.LocalIntegrationConclusion hc := by
  refine ⟨R.localActionOfTotal hc hTotal,
    R.compatibleClosedFieldAction_of_totalGraphIntertwiners hc hTotal, ?_⟩
  intro ρ hρ
  exact R.compatibleClosedFieldAction_unique hc ρ (R.localActionOfTotal hc hTotal) hρ
    (R.compatibleClosedFieldAction_of_totalGraphIntertwiners hc hTotal)

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule.UnitaryStructure

end

end OAI
