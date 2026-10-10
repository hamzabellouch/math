import OAI.Topology.ArtinGroups.ParabolicIntersections.VisualTrivialSegment
import OAI.Topology.ArtinGroups.ParabolicIntersections.WeakMalnormalAlgebra

namespace OAI

/-! The weak malnormality assertion for the edge group in CMMW Theorem 3.2,
with its published hypotheses discharged for arbitrary Artin matrices. -/
namespace HarmonicArtin.ParabolicIntersections
open TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (Y Z : Set S)
variable [hSplit : Fact (IsVisualSplit M Y Z)]
noncomputable local instance : MulAction (Artin M) (VisualVertex M Y Z) :=
  visualAction M Y Z hSplit.out

/-- The edge group of every visual splitting of an irreducible Artin group
is weakly malnormal. -/
theorem visual_edge_weaklyMalnormal (hIrred : IsIrreducible M) :
    WeaklyMalnormal (artinParabolic M (Y∩Z)) := by
  obtain ⟨u,v,_,huv⟩ := visual_exists_trivial_pair M Y Z hIrred
  obtain ⟨b,g,hg⟩ := visual_vertex_exists M Y Z u
  obtain ⟨c,h,hh⟩ := visual_vertex_exists M Y Z v
  have hsub (b : Bool) : Y∩Z⊆visualSide Y Z b := by
    cases b
    · exact Set.inter_subset_left
    · exact Set.inter_subset_right
  have hu : conjugate g (artinParabolic M (Y∩Z))≤MulAction.stabilizer (Artin M) u := by
    rw [hg,visual_vertex_stabilizer]
    exact conjugate_mono g (standard_mono M (hsub b))
  have hv : conjugate h (artinParabolic M (Y∩Z))≤MulAction.stabilizer (Artin M) v := by
    rw [hh,visual_vertex_stabilizer]
    exact conjugate_mono h (standard_mono M (hsub c))
  apply weaklyMalnormal_of_conjugates_inf_bot _ g h
  apply le_bot_iff.mp
  exact huv ▸ inf_le_inf hu hv

end HarmonicArtin.ParabolicIntersections

end OAI
