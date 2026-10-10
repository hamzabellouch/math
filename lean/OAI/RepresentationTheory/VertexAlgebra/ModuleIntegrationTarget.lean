import OAI.RepresentationTheory.VertexAlgebra.ModuleSmearedFields

namespace OAI

noncomputable section
namespace StronglyRationalVOA
universe u v
namespace LocalOperatorAlgebra
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (B : VonNeumannAlgebra H)
 

def IsNormal (π : B.toStarSubalgebra →⋆ₐ[ℂ] (K →L[ℂ] K)) : Prop :=
  ∀ (F : Filter B.toStarSubalgebra) (b : B.toStarSubalgebra),
    (∃ C : ℝ, ∀ᶠ a : B.toStarSubalgebra in F, ‖(a : H →L[ℂ] H)‖ ≤ C) →
    (∀ x y : H, Filter.Tendsto (fun a : B.toStarSubalgebra => inner ℂ x ((a : H →L[ℂ] H) y)) F
      (nhds (inner ℂ x ((b : H →L[ℂ] H) y)))) →
    ∀ x y : K, Filter.Tendsto (fun a : B.toStarSubalgebra => inner ℂ x (π a y)) F
      (nhds (inner ℂ x (π b y)))
end LocalOperatorAlgebra

namespace CFTTypeVOA.GradingRestrictedModule.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {M : A.GradingRestrictedModule W} (R : M.UnitaryStructure U)

 

abbrev LocalActionFamily (_R : M.UnitaryStructure U) (hc : A.toVertexAlgebra.C2Cofinite) :=
  ∀ I : ProperCircleArc,
    (U.intervalAlgebra hc I).toStarSubalgebra →⋆ₐ[ℂ] (Completion W →L[ℂ] Completion W)

 

def IsCompatibleClosedFieldAction (hc : A.toVertexAlgebra.C2Cofinite)
    (π : R.LocalActionFamily hc) : Prop :=
  (∀ I, LocalOperatorAlgebra.IsNormal (U.intervalAlgebra hc I) (π I)) ∧
  (∀ (I J : ProperCircleArc) (hIJ : I.carrier ⊆ J.carrier)
    (x : (U.intervalAlgebra hc I).toStarSubalgebra),
    π J ⟨x, U.localAlgebra_isotone hc hIJ x.property⟩ = π I x) ∧
  (∀ (I : ProperCircleArc) (a : V) (d : ℕ) (ha : a ∈ A.grade d)
    (f : SmoothCircleFunction) (hf : tsupport f.onCircle ⊆ I.carrier) (i j : Bool),
    π I ⟨ClosedGraphData.entry (U.closedSmoothField hc a d f)
      (U.closedSmoothField_isClosed hc ha f) i j,
      U.closedSmoothField_graphData_mem hc ha f hf i j⟩ =
      ClosedGraphData.entry (R.closedSmoothField hc a d f)
        (R.closedSmoothField_isClosed hc ha f) i j)

 

def LocalIntegrationConclusion (hc : A.toVertexAlgebra.C2Cofinite) : Prop :=
  ∃! π : R.LocalActionFamily hc, R.IsCompatibleClosedFieldAction hc π

end CFTTypeVOA.GradingRestrictedModule.UnitaryStructure
end StronglyRationalVOA

end

end OAI
