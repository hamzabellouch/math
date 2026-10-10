import OAI.Topology.ArtinGroups.ParabolicIntersections.VisualTree
import OAI.Topology.ArtinGroups.ParabolicIntersections.NormalParabolic
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeFixedPaths

namespace OAI

/-! Proper stabilizers and branching in the visual Bass--Serre tree. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S) (Y Z : Set S)
variable [hSplit : Fact (IsVisualSplit M Y Z)]
noncomputable local instance : MulAction (Artin M) (VisualVertex M Y Z) :=
  visualAction M Y Z hSplit.out

omit [Fintype S] in
lemma visual_preservesAdj : TreeAction.PreservesAdj (G := Artin M) (visualGraph M Y Z) := by
  intro g u v h
  exact (AmalgamTree.translate (visualEdgeInclusion M Y Z)
    (visualFromArtin M Y Z hSplit.out g)).map_adj h

lemma visual_vertex_proper (v : VisualVertex M Y Z) :
    MulAction.stabilizer (Artin M) v≠⊤ := by
  obtain ⟨b,g,rfl⟩ := visual_vertex_exists M Y Z v
  rw [visual_vertex_stabilizer]
  intro he
  have he' := congrArg (conjugate g⁻¹) he
  rw [conjugate_inv_cancel,conjugate_top] at he'
  apply standard_ne_top_of_ne_univ M _ he'
  cases b
  · exact (Set.ssubset_iff_subset_ne.mp hSplit.out.2.1).2
  · exact (Set.ssubset_iff_subset_ne.mp hSplit.out.2.2.1).2

/-- Every direction at every vertex can be moved by its stabilizer. -/
lemma visual_branching (v w : VisualVertex M Y Z) (h : (visualGraph M Y Z).Adj v w) :
    ∃ a : Artin M, a • v=v ∧ a • w≠w := by
  have hn : ¬MulAction.stabilizer (Artin M) v≤MulAction.stabilizer (Artin M) w := by
    intro hle
    apply visual_vertex_proper M Y Z w
    have he := visual_adj_stabilizers_generate M Y Z h
    rwa [sup_eq_right.mpr hle] at he
  obtain ⟨a,ha,hna⟩ := SetLike.not_le_iff_exists.mp hn
  exact ⟨a,ha,hna⟩

end HarmonicArtin.ParabolicIntersections

end OAI
