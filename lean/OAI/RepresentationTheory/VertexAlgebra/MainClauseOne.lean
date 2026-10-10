import OAI.RepresentationTheory.VertexAlgebra.ConformalNetContinuation
import OAI.RepresentationTheory.VertexAlgebra.SourceStrongRationality

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

theorem source_main_clause_one (_hSimple : A.toVertexAlgebra.IsSimple)
    (hSR : A.IsStronglyRational.{u,v}) :
    A.PolynomialEnergyBounds ∧ U.CKLWStrongLocal hSR.2.2 ∧
      Nonempty (IrreducibleConformalNetStructure (U.intervalAlgebra hSR.2.2)) :=
  ⟨U.polynomialEnergyBounds hSR.2.2,U.cklwStrongLocal_and_conformalNet hSR.2.2⟩
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
