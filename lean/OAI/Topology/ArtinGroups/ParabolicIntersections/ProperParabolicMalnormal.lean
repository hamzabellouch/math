import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeBridge
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeInvariantTranslate
import OAI.Topology.ArtinGroups.ParabolicIntersections.VisualParabolicSubtree
import OAI.Topology.ArtinGroups.ParabolicIntersections.VisualEdgeTransitive
import OAI.Topology.ArtinGroups.ParabolicIntersections.VisualFactorMalnormal

namespace OAI

/-!
# Weak malnormality of all proper parabolics

This proves the implication needed from Charney--Martin--Morris-Wright,
*Acylindrical hyperbolicity for Artin groups with a visual splitting*,
Algebraic & Geometric Topology 26 (2026), Proposition 4.2, for the present
Artin groups. A proper parabolic preserves a proper convex subtree. Two
translates can be placed at the ends of a segment with trivial stabilizer.
Their common stabilizer fixes that segment, hence is trivial.
-/
namespace HarmonicArtin.ParabolicIntersections
open TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (Y Z : Set S)
variable [hSplit : Fact (IsVisualSplit M Y Z)]
noncomputable local instance properParabolicAction : MulAction (Artin M) (VisualVertex M Y Z) :=
  visualAction M Y Z hSplit.out
include hSplit

/-- The two conjugates have trivial intersection; this is stronger than
finiteness in the published weak-malnormality criterion. -/
theorem standard_parabolic_trivial_conjugates (hIrred : IsIrreducible M)
    (X : Set S) (hX : X≠Set.univ) :
    ∃ a b : Artin M,
      conjugate a (artinParabolic M X) ⊓ conjugate b (artinParabolic M X)=⊥ := by
  let U := parabolicSubtree M Y Z X
  have hU : PathClosed (visualGraph M Y Z) U := parabolicSubtree_pathClosed M Y Z X
  obtain ⟨x,y,hxy,hx,hy⟩ := parabolicSubtree_boundary M Y Z hIrred X hX
  obtain ⟨u,v,huv,hu,hv,hpair⟩ := visual_trivial_pair_distinct_type M Y Z hIrred x.1
  obtain ⟨p,hp⟩ := (visualGraph_isTree M Y Z).connected.exists_isPath u v
  have hpn : ¬p.Nil := SimpleGraph.Walk.not_nil_of_ne huv
  have hprn : ¬p.reverse.Nil := SimpleGraph.Walk.not_nil_of_ne huv.symm
  obtain ⟨a,hax,hay⟩ := visual_oriented_edge_transitive M Y Z hxy
    (p.adj_snd hpn) hu.symm
  obtain ⟨b,hbx,hby⟩ := visual_oriented_edge_transitive M Y Z hxy
    (p.reverse.adj_snd hprn) hv.symm
  refine ⟨a,b,?_⟩
  apply le_antisymm _ bot_le
  intro g hg
  have haU : u∈(a • ·) '' U := ⟨x,hx,hax⟩
  have hbU : v∈(b • ·) '' U := ⟨x,hx,hbx⟩
  have hpa : p.snd∉(a • ·) '' U := not_mem_image_of_smul_eq hy hay
  have hpb : p.reverse.snd∉(b • ·) '' U := not_mem_image_of_smul_eq hy hby
  have hfix := fixes_bridge (visualGraph M Y Z) (visualGraph_isTree M Y Z)
    (visual_preservesAdj M Y Z)
    (pathClosed_smul _ (visual_preservesAdj M Y Z) hU a)
    (pathClosed_smul _ (visual_preservesAdj M Y Z) hU b)
    haU hbU p hp hpa hpb g
    (fun w hw => conjugate_preserves_image (artinParabolic M X) U
      (fun q hq z hz => parabolicSubtree_invariant M Y Z X hq hz) a hg.1 hw)
    (fun w hw => conjugate_preserves_image (artinParabolic M X) U
      (fun q hq z hz => parabolicSubtree_invariant M Y Z X hq hz) b hg.2 hw)
  have hgpair : g∈pairStabilizer (G := Artin M) u v := hfix
  rwa [hpair] at hgpair

/-- Every proper parabolic of an irreducible visually split Artin group
is weakly malnormal, with no published hypotheses. -/
theorem proper_parabolic_weaklyMalnormal (hIrred : IsIrreducible M)
    (P : Subgroup (Artin M)) (hP : IsParabolic M P) (hne : P≠⊤) : WeaklyMalnormal P := by
  obtain ⟨X,g,rfl⟩ := hP
  have hX : X≠Set.univ := by
    intro he
    apply hne
    rw [he,standard_univ,conjugate_top]
  obtain ⟨a,b,hab⟩ := standard_parabolic_trivial_conjugates M Y Z hIrred X hX
  exact (weaklyMalnormal_of_conjugates_inf_bot _ a b hab).conjugate_subgroup g

end HarmonicArtin.ParabolicIntersections

end OAI
