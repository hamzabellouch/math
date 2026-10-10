import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeAvoidingGraph
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeTripod
import OAI.Topology.ArtinGroups.ParabolicIntersections.GraphWalkLevels

namespace OAI

/-! Interior segments and prefixes in the shortcut metric. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (u v : V)

lemma tree_walk_level (hT : T.IsTree) (hA : PreservesAdj (G := G) T)
    (hne : u≠v) (hnadj : ¬T.Adj u v) {x y : V}
    (p : T.Walk x y) (k : ℕ) (hk : k ≤ (avoidingGraph (G := G) T u v).dist x y) :
    ∃ w∈p.support,(avoidingGraph (G := G) T u v).dist x w=k := by
  let H := avoidingGraph (G := G) T u v
  have hH := avoidingGraph_connected T u v hT hA hne hnadj
  have hle := le_avoidingGraph T u v hT.isAcyclic hA hne hnadj
  obtain ⟨w,hw,hd⟩ := walk_exists_dist_level H hH x (p.mapLe hle) k (by simp) hk
  exact ⟨w,by simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hw,hd⟩

/-- A long shortcut path contains a translate of the fixed segment
well inside both ends, and at bounded distance from its first end. -/
theorem exists_interior_segment (hT : T.IsTree) (hA : PreservesAdj (G := G) T)
    (hne : u≠v) (hnadj : ¬T.Adj u v) {x y : V}
    (p : T.Walk x y) (hp : p.IsPath) (r : ℕ)
    (hxy : 2*r+10 ≤ (avoidingGraph (G := G) T u v).dist x y) :
    ∃ g : G, ∀ w∈({u,v} : Set V), g • w∈p.support ∧
      r+1 < (avoidingGraph (G := G) T u v).dist x (g • w) ∧
      r+1 < (avoidingGraph (G := G) T u v).dist y (g • w) ∧
      (avoidingGraph (G := G) T u v).dist x (g • w) ≤ r+8 := by
  let H := avoidingGraph (G := G) T u v
  have hH := avoidingGraph_connected T u v hT hA hne hnadj
  have hS := avoidingGraph_pathSaturated (G := G) T u v hT.isAcyclic
  obtain ⟨a,ha,hda⟩ := tree_walk_level T u v hT hA hne hnadj p (r+5) (by omega)
  have hay : 2 ≤ H.dist a y := by
    have hh := hH.dist_triangle (u := x) (v := a) (w := y)
    change H.dist x a=r+5 at hda
    change 2*r+10 ≤ H.dist x y at hxy
    dsimp only [H] at *
    omega
  let s := p.dropUntil a ha
  have hs : s.IsPath := hp.dropUntil ha
  obtain ⟨b,hb,hdb⟩ := tree_walk_level T u v hT hA hne hnadj s 2 hay
  let t := s.takeUntil b hb
  have ht : t.IsPath := hs.takeUntil hb
  have hseg : ContainsSegment (G := G) u v T t := by
    by_contra hn
    have hab : a≠b := by
      intro he
      subst b
      simp at hdb
    have hadj := avoidingGraph_subpath T u v hT.isAcyclic t hn
      t.start_mem_support t.end_mem_support hab
    have hd := H.dist_eq_one_iff_adj.mpr hadj
    change H.dist a b=2 at hdb
    omega
  obtain ⟨g,hgu,hgv⟩ := hseg
  refine ⟨g,?_⟩
  intro w hw
  have hgw : g • w∈t.support := by
    rcases Set.mem_insert_iff.mp hw with he|he
    · exact he ▸ hgu
    · exact Set.mem_singleton_iff.mp he ▸ hgv
  have hdist := shortcut_dist_split T H hT hH hS t ht hgw
  change H.dist a b=2 at hdb
  have hnear : H.dist a (g • w) ≤ 3 := by omega
  have hmem : g • w∈p.support :=
    p.support_dropUntil_subset_support ha (s.support_takeUntil_subset_support hb hgw)
  have hx := hH.dist_triangle (u := x) (v := g • w) (w := a)
  have hy := hH.dist_triangle (u := x) (v := a) (w := g • w)
  have hz := hH.dist_triangle (u := x) (v := g • w) (w := y)
  rw [H.dist_comm (u := g • w) (v := a)] at hx
  rw [H.dist_comm (u := g • w) (v := y)] at hz
  refine ⟨hmem,?_,?_,?_⟩ <;> dsimp only [H] at * <;> omega

lemma bounded_vertices_in_prefix (H : SimpleGraph V) (hT : T.IsTree)
    (hH : H.Connected) (hS : PathSaturated T H) {x y b w : V}
    (p : T.Walk x y) (hp : p.IsPath) (hb : b∈p.support) (hw : w∈p.support)
    (K : ℕ) (hdb : H.dist x b=K+2) (hdw : H.dist x w ≤ K) :
    w∈(p.takeUntil b hb).support := by
  rcases prefixes_comparable T p hw hb with h|h
  · exact h
  · have hh := shortcut_dist_split T H hT hH hS (p.takeUntil w hw) (hp.takeUntil hw) h
    omega

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
