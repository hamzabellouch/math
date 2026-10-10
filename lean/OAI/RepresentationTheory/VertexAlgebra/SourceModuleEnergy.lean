import OAI.RepresentationTheory.VertexAlgebra.ModuleEnergyMain

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 
theorem source_module_energy
    (hSimple : A.toVertexAlgebra.IsSimple) (hSR : A.IsStronglyRational.{u,v})
    {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (M : A.GradingRestrictedModule W) (R : M.UnitaryStructure U) :
    M.SourceEnergyConclusion U :=
  R.source_energy_theorem hSimple hSR
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
