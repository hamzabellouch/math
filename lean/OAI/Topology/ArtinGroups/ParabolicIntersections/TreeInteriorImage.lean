import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeShortcutMetric
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeActionDefinitions
import OAI.Topology.ArtinGroups.ParabolicIntersections.GraphMetric

namespace OAI

/-! Small endpoint displacement preserves the interior of a tree path. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {G V : Type} [Group G] [MulAction G V]
variable (T H : SimpleGraph V)

lemma image_mem_of_deep (hT : T.IsTree) (hH : H.Connected)
    (hS : PathSaturated T H) (hA : PreservesAdj (G := G) T)
    (hB : PreservesAdj (G := G) H) {x y w : V} (p : T.Walk x y) (hp : p.IsPath)
    (hw : w∈p.support) (r : ℕ) (hx : r+1 < H.dist x w) (hy : r+1 < H.dist y w)
    (g : G) (hgx : H.dist x (g • x) ≤ r) (hgy : H.dist y (g • y) ≤ r) :
    g • w∈p.support := by
  obtain ⟨a,ha⟩ := hT.connected.exists_isPath (g • x) x
  obtain ⟨b,hb⟩ := hT.connected.exists_isPath y (g • y)
  let q := p.map (translate T hA g)
  have hq : q.IsPath := hp.map (MulAction.toPerm g).injective
  have hgw : g • w∈q.support := by
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨w,hw,rfl⟩
  have hm := path_support_subset_walk T hT.isAcyclic q hq ((a.append p).append b) hgw
  rcases (SimpleGraph.Walk.mem_support_append_iff (a.append p) b).mp hm with hm|hm
  · rcases (SimpleGraph.Walk.mem_support_append_iff a p).mp hm with hm|hm
    · have h := shortcut_dist_split T H hT hH hS a ha hm
      rw [graph_action_dist H hH hB g x w,
        H.dist_comm (u := g • x) (v := x)] at h
      omega
    · exact hm
  · have h := shortcut_dist_split T H hT hH hS b hb hm
    rw [H.dist_comm (u := g • w) (v := g • y),
      graph_action_dist H hH hB g y w] at h
    omega

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
