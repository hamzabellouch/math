import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeBranchingHyperbolic
import OAI.Topology.ArtinGroups.ParabolicIntersections.VisualInfiniteBranching

namespace OAI

/-!
# An unconditional acylindrical action for the Artin visual splitting

The sufficient Artin case of Minasyan--Osin (2015), Corollary 2.2,
is proved here by constructing a geodesic hyperbolic realization of the
shortcut graph, a uniform acylindricity bound, and three distinct orbit
limit points. No instance of the published amalgam criterion is assumed.
-/
namespace HarmonicArtin.ParabolicIntersections
open TreeAction
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (Y Z : Set S)
variable [hSplit : Fact (IsVisualSplit M Y Z)]
noncomputable local instance visualAcylindricalAction : MulAction (Artin M) (VisualVertex M Y Z) :=
  visualAction M Y Z hSplit.out

include hSplit in
theorem visual_acylindricallyHyperbolic (hIrred : IsIrreducible M) :
    AcylindricallyHyperbolic (Artin M) := by
  obtain ⟨u,v,hne,hu,hv,hfree⟩ := visual_trivial_pair_distinct_type M Y Z hIrred false
  apply acylindricallyHyperbolic_of_free_segment (visualGraph M Y Z)
    (visualGraph_isTree M Y Z) (visual_preservesAdj M Y Z) ?_ u v hne ?_ hfree
  · intro x y hxy
    obtain ⟨a,ha,hinj⟩ := visual_infinite_branching M Y Z hxy
    exact ⟨a,ha,hinj⟩
  · intro h
    exact h.1 (hu.trans hv.symm)

end HarmonicArtin.ParabolicIntersections

end OAI
