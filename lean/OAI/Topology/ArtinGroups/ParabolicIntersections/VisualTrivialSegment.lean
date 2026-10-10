import OAI.Topology.ArtinGroups.ParabolicIntersections.VisualTreeProperties
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeMinimalNormal
import OAI.Topology.ArtinGroups.ParabolicIntersections.ParabolicMinimal
import OAI.Topology.ArtinGroups.ParabolicIntersections.ParabolicCore

namespace OAI

/-! The visual tree has a segment with trivial pointwise stabilizer.
This proves the segment step in CMMW (2026), Theorem 3.2, using the
unconditional parabolic intersection theorem and rank descent. -/
namespace HarmonicArtin.ParabolicIntersections
open TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (Y Z : Set S)
variable [hSplit : Fact (IsVisualSplit M Y Z)]
noncomputable local instance : MulAction (Artin M) (VisualVertex M Y Z) :=
  visualAction M Y Z hSplit.out

lemma visual_pair_isParabolic (u v : VisualVertex M Y Z) :
    IsParabolic M (pairStabilizer (G := Artin M) u v) := by
  obtain ⟨X,g,hg⟩ := visual_vertex_isParabolic M Y Z u
  obtain ⟨X',g',hg'⟩ := visual_vertex_isParabolic M Y Z v
  change IsParabolic M (MulAction.stabilizer (Artin M) u ⊓ MulAction.stabilizer (Artin M) v)
  rw [hg,hg']
  exact unconditional_parabolic_intersections M X X' g g'

/-- A finite segment of the genuine Bass--Serre tree has trivial stabilizer. -/
theorem visual_exists_trivial_pair (hIrred : IsIrreducible M) :
    ∃ u v : VisualVertex M Y Z, u≠v ∧ pairStabilizer (G := Artin M) u v=⊥ := by
  let F : Set (Subgroup (Artin M)) :=
    {P | ∃ u v : VisualVertex M Y Z, u≠v ∧ P=pairStabilizer (G := Artin M) u v}
  have hF : F.Nonempty := by
    let u := visualVertex M Y Z hSplit.out false 1
    let v := visualVertex M Y Z hSplit.out true 1
    exact ⟨pairStabilizer (G := Artin M) u v,u,v,
      (visual_vertex_adj M Y Z 1).ne,rfl⟩
  obtain ⟨P,hP,hmin⟩ := exists_minimal_parabolic M F hF (by
    rintro P ⟨u,v,_,rfl⟩
    exact visual_pair_isParabolic M Y Z u v)
  obtain ⟨u,v,hne,rfl⟩ := hP
  have hmin' : ∀ a b : VisualVertex M Y Z, a≠b →
      pairStabilizer (G := Artin M) a b≤pairStabilizer (G := Artin M) u v →
      pairStabilizer (G := Artin M) a b=pairStabilizer (G := Artin M) u v := by
    intro a b hab hle
    exact hmin _ ⟨a,b,hab,rfl⟩ hle
  obtain ⟨p,hp⟩ := (visualGraph_isTree M Y Z).connected.exists_isPath v u
  have hn := minimal_pair_normal (visualGraph M Y Z) (visualGraph_isTree M Y Z).isAcyclic
    (visual_preservesAdj M Y Z) u v hne hmin' p hp
    (visual_branching M Y Z) (fun _ _ h => visual_adj_stabilizers_generate M Y Z h)
  have hproper : pairStabilizer (G := Artin M) u v≠⊤ := by
    intro he
    apply visual_vertex_proper M Y Z u
    exact top_le_iff.mp (he ▸ (inf_le_left : pairStabilizer (G := Artin M) u v≤_))
  exact ⟨u,v,hne,(normal_parabolic M hIrred _ (visual_pair_isParabolic M Y Z u v) hn).resolve_right hproper⟩

end HarmonicArtin.ParabolicIntersections

end OAI
