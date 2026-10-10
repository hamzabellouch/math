import OAI.RepresentationTheory.VertexAlgebra.ModuleIntegrationTarget
import OAI.RepresentationTheory.VertexAlgebra.GeneratedIntertwinerAction

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA
open UniformSpace
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}

 
structure LocalSmear (A : CFTTypeVOA V) (I : ProperCircleArc) where
  state : V
  weight : ℕ
  homogeneous : state ∈ A.grade weight
  test : SmoothCircleFunction
  supported : tsupport test.onCircle ⊆ I.carrier

abbrev LocalGraphIndex (A : CFTTypeVOA V) (I : ProperCircleArc) := LocalSmear A I × Bool × Bool

def LocalGraphIndex.transpose {I : ProperCircleArc} (g : LocalGraphIndex A I) :
    LocalGraphIndex A I := (g.1, g.2.2, g.2.1)

namespace UnitaryStructure
variable (U)
def localGraphGenerator (hc : A.toVertexAlgebra.C2Cofinite) (I : ProperCircleArc)
    (g : LocalGraphIndex A I) : Completion V →L[ℂ] Completion V :=
  ClosedGraphData.entry (U.closedSmoothField hc g.1.state g.1.weight g.1.test)
    (U.closedSmoothField_isClosed hc g.1.homogeneous g.1.test) g.2.1 g.2.2

theorem localGraphGenerator_star (hc : A.toVertexAlgebra.C2Cofinite) (I : ProperCircleArc)
    (g : LocalGraphIndex A I) : star (U.localGraphGenerator hc I g) =
      U.localGraphGenerator hc I g.transpose :=
  ClosedGraphData.star_entry _ _ _ _

theorem range_localGraphGenerator (hc : A.toVertexAlgebra.C2Cofinite) (I : ProperCircleArc) :
    Set.range (U.localGraphGenerator hc I) = U.localGraphData hc I.carrier := by
  ext x
  constructor
  · rintro ⟨⟨a, i, j⟩, rfl⟩
    exact ⟨a.state, a.weight, a.homogeneous, a.test, a.supported, i, j, rfl⟩
  · rintro ⟨a, d, ha, f, hf, i, j, rfl⟩
    exact ⟨(⟨a, d, ha, f, hf⟩, i, j), rfl⟩
end UnitaryStructure

namespace GradingRestrictedModule.UnitaryStructure
variable {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {M : A.GradingRestrictedModule W} (R : M.UnitaryStructure U)

def localGraphGenerator (hc : A.toVertexAlgebra.C2Cofinite) (I : ProperCircleArc)
    (g : LocalGraphIndex A I) : Completion W →L[ℂ] Completion W :=
  ClosedGraphData.entry (R.closedSmoothField hc g.1.state g.1.weight g.1.test)
    (R.closedSmoothField_isClosed hc g.1.homogeneous g.1.test) g.2.1 g.2.2

theorem localGraphGenerator_star (hc : A.toVertexAlgebra.C2Cofinite) (I : ProperCircleArc)
    (g : LocalGraphIndex A I) : star (R.localGraphGenerator hc I g) =
      R.localGraphGenerator hc I g.transpose :=
  ClosedGraphData.star_entry _ _ _ _

 

def LocalGraphIntertwiner (hc : A.toVertexAlgebra.C2Cofinite) (I : ProperCircleArc) :=
  {T : Completion V →L[ℂ] Completion W // ∀ g : LocalGraphIndex A I,
    (R.localGraphGenerator hc I g).comp T = T.comp (U.localGraphGenerator hc I g)}

def localGraphIntertwinerMap (hc : A.toVertexAlgebra.C2Cofinite) (I : ProperCircleArc) :
    R.LocalGraphIntertwiner hc I → Completion V →L[ℂ] Completion W := Subtype.val

 

def HasTotalLocalGraphIntertwiners (hc : A.toVertexAlgebra.C2Cofinite) : Prop :=
  ∀ I : ProperCircleArc, DenseRange (BoundedIntertwiner.core (R.localGraphIntertwinerMap hc I))

theorem graphIntertwiners_gram_commutes (hc : A.toVertexAlgebra.C2Cofinite) (I : ProperCircleArc)
    (b : (U.intervalAlgebra hc I).toStarSubalgebra) (S T : R.LocalGraphIntertwiner hc I) :
    Commute (S.val.adjoint.comp T.val) (b : Completion V →L[ℂ] Completion V) := by
  have hmem : b.val ∈ (LocalOperatorAlgebra.generated
      (Set.range (U.localGraphGenerator hc I))).toStarSubalgebra := by
    rw [U.range_localGraphGenerator]
    exact b.property
  exact BoundedIntertwiner.gram_commutes_generated
    (U.localGraphGenerator hc I) (R.localGraphGenerator hc I) LocalGraphIndex.transpose
    (U.localGraphGenerator_star hc I) (R.localGraphGenerator_star hc I)
    (R.localGraphIntertwinerMap hc I) (fun g T => T.property g) ⟨b, hmem⟩ S T

 

def localActionOfTotal (hc : A.toVertexAlgebra.C2Cofinite)
    (hTotal : R.HasTotalLocalGraphIntertwiners hc) : R.LocalActionFamily hc :=
  fun I => BoundedIntertwiner.representation (U.intervalAlgebra hc I).toStarSubalgebra
    (R.localGraphIntertwinerMap hc I) (hTotal I) (R.graphIntertwiners_gram_commutes hc I)

theorem localActionOfTotal_intertwines (hc : A.toVertexAlgebra.C2Cofinite)
    (hTotal : R.HasTotalLocalGraphIntertwiners hc) (I : ProperCircleArc)
    (b : (U.intervalAlgebra hc I).toStarSubalgebra) (T : R.LocalGraphIntertwiner hc I)
    (x : Completion V) : R.localActionOfTotal hc hTotal I b (T.val x) = T.val (b.val x) :=
  BoundedIntertwiner.representation_intertwines _ _ _ _ _ _ _

theorem localActionOfTotal_normal (hc : A.toVertexAlgebra.C2Cofinite)
    (hTotal : R.HasTotalLocalGraphIntertwiners hc) (I : ProperCircleArc) :
    LocalOperatorAlgebra.IsNormal (U.intervalAlgebra hc I) (R.localActionOfTotal hc hTotal I) :=
  BoundedIntertwiner.representation_preserves_boundedWOT _ _ _ _

theorem localActionOfTotal_generator (hc : A.toVertexAlgebra.C2Cofinite)
    (hTotal : R.HasTotalLocalGraphIntertwiners hc) (I : ProperCircleArc) (g : LocalGraphIndex A I) :
    R.localActionOfTotal hc hTotal I ⟨U.localGraphGenerator hc I g,
      U.closedSmoothField_graphData_mem hc g.1.homogeneous g.1.test g.1.supported g.2.1 g.2.2⟩ =
        R.localGraphGenerator hc I g := by
  apply BoundedIntertwiner.ext_of_total (R.localGraphIntertwinerMap hc I) (hTotal I)
  intro T x
  change R.localActionOfTotal hc hTotal I _ (T.val x) = R.localGraphGenerator hc I g (T.val x)
  rw [R.localActionOfTotal_intertwines]
  exact congrArg (fun D : Completion V →L[ℂ] Completion W => D x) (T.property g).symm

 
def LocalGraphIntertwiner.restrict (hc : A.toVertexAlgebra.C2Cofinite)
    {I J : ProperCircleArc} (hIJ : I.carrier ⊆ J.carrier)
    (T : R.LocalGraphIntertwiner hc J) : R.LocalGraphIntertwiner hc I :=
  ⟨T.val, fun g => T.property (⟨g.1.state, g.1.weight, g.1.homogeneous,
    g.1.test, g.1.supported.trans hIJ⟩, g.2.1, g.2.2)⟩

theorem localActionOfTotal_compatible (hc : A.toVertexAlgebra.C2Cofinite)
    (hTotal : R.HasTotalLocalGraphIntertwiners hc)
    (I J : ProperCircleArc) (hIJ : I.carrier ⊆ J.carrier)
    (b : (U.intervalAlgebra hc I).toStarSubalgebra) :
    R.localActionOfTotal hc hTotal J ⟨b, U.localAlgebra_isotone hc hIJ b.property⟩ =
      R.localActionOfTotal hc hTotal I b := by
  apply BoundedIntertwiner.ext_of_total (R.localGraphIntertwinerMap hc J) (hTotal J)
  intro T x
  change R.localActionOfTotal hc hTotal J _ (T.val x) =
    R.localActionOfTotal hc hTotal I b (T.val x)
  rw [R.localActionOfTotal_intertwines]
  exact (R.localActionOfTotal_intertwines hc hTotal I b
    (LocalGraphIntertwiner.restrict R hc hIJ T) x).symm

 

theorem compatibleClosedFieldAction_of_totalGraphIntertwiners
    (hc : A.toVertexAlgebra.C2Cofinite) (hTotal : R.HasTotalLocalGraphIntertwiners hc) :
    R.IsCompatibleClosedFieldAction hc (R.localActionOfTotal hc hTotal) := by
  refine ⟨R.localActionOfTotal_normal hc hTotal,
    R.localActionOfTotal_compatible hc hTotal, ?_⟩
  intro I a d ha f hf i j
  exact R.localActionOfTotal_generator hc hTotal I (⟨a,d,ha,f,hf⟩,i,j)

end GradingRestrictedModule.UnitaryStructure
end StronglyRationalVOA.CFTTypeVOA

end

end OAI
