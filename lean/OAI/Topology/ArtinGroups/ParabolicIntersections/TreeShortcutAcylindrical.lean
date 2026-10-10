import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeSegmentCount
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeShortcutPosition
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeInteriorImage

namespace OAI

/-! Uniform acylindricity of the graph obtained by coning off segment-free paths. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (u v : V)

/-- The constants depend only on displacement and on the chosen free
segment, even when the original tree has infinite-valence vertices. -/
theorem avoidingGraph_acylindrical_count (hT : T.IsTree)
    (hA : PreservesAdj (G := G) T) (hfree : pairStabilizer (G := G) u v=⊥)
    (hne : u≠v) (hnadj : ¬T.Adj u v) (r : ℕ) (x y : V)
    (hxy : 2*r+10 ≤ (avoidingGraph (G := G) T u v).dist x y) :
    {g : G | (avoidingGraph (G := G) T u v).dist x (g • x) ≤ r ∧
      (avoidingGraph (G := G) T u v).dist y (g • y) ≤ r}.Finite ∧
    {g : G | (avoidingGraph (G := G) T u v).dist x (g • x) ≤ r ∧
      (avoidingGraph (G := G) T u v).dist y (g • y) ≤ r}.ncard ≤
        (2*r+10)*(2*T.dist u v+1)^2 := by
  let H := avoidingGraph (G := G) T u v
  have hH : H.Connected := avoidingGraph_connected T u v hT hA hne hnadj
  have hS : PathSaturated T H := avoidingGraph_pathSaturated T u v hT.isAcyclic
  have hB : PreservesAdj (G := G) H := avoidingGraph_preservesAdj T u v hA
  obtain ⟨p,hp⟩ := hT.connected.exists_isPath x y
  obtain ⟨a,ha⟩ := exists_interior_segment T u v hT hA hne hnadj p hp r hxy
  obtain ⟨b,hb,hdb⟩ := tree_walk_level T u v hT hA hne hnadj p (2*r+10) hxy
  let q := p.takeUntil b hb
  have hq : q.IsPath := hp.takeUntil hb
  let A : Set G := {g | H.dist x (g • x) ≤ r ∧ H.dist y (g • y) ≤ r}
  let B := segmentOccurrences (G := G) u v T q
  have hmap : ∀ g∈A,g*a∈B := by
    intro g hg
    have hm (w : V) (hw : w∈({u,v} : Set V)) : (g*a) • w∈q.support := by
      obtain ⟨hmem,hleft,hright,hupper⟩ := ha w hw
      have himage : g • (a • w)∈p.support :=
        image_mem_of_deep T H hT hH hS hA hB p hp hmem r hleft hright g hg.1 hg.2
      have hdist : H.dist x (g • (a • w)) ≤ 2*r+8 := by
        have htri := hH.dist_triangle (u := x) (v := g • x) (w := g • (a • w))
        rw [graph_action_dist H hH hB g x (a • w)] at htri
        have hgx : H.dist x (g • x) ≤ r := hg.1
        change H.dist x (a • w) ≤ r+8 at hupper
        omega
      rw [mul_smul]
      exact bounded_vertices_in_prefix T H hT hH hS p hp hb himage (2*r+8)
        (by simpa only [Nat.add_assoc] using hdb) hdist
    exact ⟨hm u (by simp),hm v (by simp)⟩
  have hinj : Function.Injective (fun g : G => g*a) := fun _ _ h => mul_right_cancel h
  have hfinB : B.Finite := segmentOccurrences_finite hfree T q
  have hfinA : A.Finite := (hfinB.preimage hinj.injOn).subset hmap
  refine ⟨hfinA,?_⟩
  calc
    A.ncard ≤ B.ncard := Set.ncard_le_ncard_of_injOn (fun g : G => g*a) hmap hinj.injOn hfinB
    _ ≤ H.dist x b*(2*T.dist u v+1)^2 :=
      segmentOccurrences_bound_dist T u v hT hA hfree hne hnadj q hq
    _ = (2*r+10)*(2*T.dist u v+1)^2 := by rw [hdb]

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
