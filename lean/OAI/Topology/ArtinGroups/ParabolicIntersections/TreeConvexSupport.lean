import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeActionDefinitions

namespace OAI

/-! Convexity of connected subgraphs, including the support of any walk. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {V : Type} (T : SimpleGraph V)

lemma connected_subgraph_pathClosed (hT : T.IsAcyclic) (H : T.Subgraph)
    (hH : H.Connected) : PathClosed T H.verts := by
  intro x y hx hy p hp w hw
  obtain ⟨q,hq⟩ := (hH ⟨x,hx⟩ ⟨y,hy⟩).exists_isPath
  have hqm : (q.map H.hom).IsPath := hq.map H.hom_injective
  have he : q.map H.hom=p :=
    congrArg Subtype.val (hT.subsingleton_path x y |>.elim ⟨_,hqm⟩ ⟨p,hp⟩)
  have hw' : w∈(q.map H.hom).support := he.symm ▸ hw
  rw [SimpleGraph.Walk.support_map] at hw'
  obtain ⟨z,_,hz⟩ := List.mem_map.mp hw'
  exact hz ▸ z.property

lemma walk_support_pathClosed (hT : T.IsAcyclic) {x y : V} (p : T.Walk x y) :
    PathClosed T {w | w∈p.support} := by
  rw [←p.verts_toSubgraph]
  exact connected_subgraph_pathClosed T hT p.toSubgraph p.toSubgraph_connected

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
