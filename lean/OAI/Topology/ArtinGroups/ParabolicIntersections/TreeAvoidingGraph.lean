import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeSegmentOccurrences
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeConvexSupport
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeShortcutMetric

namespace OAI

/-!
# Coning off paths that avoid a fixed orbit of segments

The vertices remain those of the original tree. A new edge joins the
endpoints of a path containing no translate of the chosen segment.
-/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (u v : V)

def avoidingGraph : SimpleGraph V where
  Adj x y := x≠y ∧ ∀ p : T.Walk x y,p.IsPath → ¬ContainsSegment (G := G) u v T p
  symm := ⟨by
    intro x y h
    refine ⟨h.1.symm,?_⟩
    intro p hp
    have hn := h.2 p.reverse hp.reverse
    simpa only [ContainsSegment,segmentOccurrences_reverse] using hn⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

lemma avoidingGraph_subpath (hT : T.IsAcyclic) {x y a b : V}
    (p : T.Walk x y) (hn : ¬ContainsSegment (G := G) u v T p)
    (ha : a∈p.support) (hb : b∈p.support) (hab : a≠b) :
    (avoidingGraph (G := G) T u v).Adj a b := by
  refine ⟨hab,?_⟩
  intro q hq hbad
  obtain ⟨g,hgu,hgv⟩ := hbad
  have hc := walk_support_pathClosed T hT p ha hb q hq
  exact hn ⟨g,hc _ hgu,hc _ hgv⟩

lemma avoidingGraph_preservesAdj (hA : PreservesAdj (G := G) T) :
    PreservesAdj (G := G) (avoidingGraph (G := G) T u v) := by
  intro g x y hxy
  refine ⟨fun he => hxy.1 ((MulAction.toPerm g).injective he),?_⟩
  intro p hp hbad
  let q := (p.map (translate T hA g⁻¹)).copy (inv_smul_smul g x) (inv_smul_smul g y)
  have hq : q.IsPath := by
    apply (SimpleGraph.Walk.isPath_copy _ _ _).mpr
    exact hp.map (MulAction.toPerm g⁻¹).injective
  apply hxy.2 q hq
  obtain ⟨a,ha⟩ := hbad
  refine ⟨g⁻¹*a,?_⟩
  have hm := (segmentOccurrences_map u v T hA p g⁻¹ (g⁻¹*a)).mpr ?_
  · change (g⁻¹*a) • u∈q.support ∧ (g⁻¹*a) • v∈q.support
    have hsup : q.support=(p.map (translate T hA g⁻¹)).support :=
      SimpleGraph.Walk.support_copy _ _ _
    rw [hsup]
    exact hm
  · simpa only [inv_inv,mul_inv_cancel_left] using ha

/-- If the chosen segment has at least two edges, every original edge
remains an edge after coning. -/
lemma le_avoidingGraph (hT : T.IsAcyclic) (hA : PreservesAdj (G := G) T)
    (hne : u≠v) (hnadj : ¬T.Adj u v) : T≤avoidingGraph (G := G) T u v := by
  intro x y hxy
  refine ⟨hxy.ne,?_⟩
  intro p hp hbad
  have he : p=hxy.toWalk :=
    congrArg Subtype.val (hT.subsingleton_path x y |>.elim ⟨p,hp⟩ ⟨_,.of_adj hxy⟩)
  obtain ⟨g,hgu,hgv⟩ := hbad
  rw [he] at hgu hgv
  simp only [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil,
    List.mem_cons,List.not_mem_nil,or_false] at hgu hgv
  have hadj : T.Adj (g • u) (g • v) := by
    rcases hgu with hx|hy <;> rcases hgv with hx'|hy'
    · exact False.elim (hne ((MulAction.toPerm g).injective (hx.trans hx'.symm)))
    · rw [hx,hy']
      exact hxy
    · rw [hy,hx']
      exact hxy.symm
    · exact False.elim (hne ((MulAction.toPerm g).injective (hy.trans hy'.symm)))
  have h := hA g⁻¹ hadj
  simp only [inv_smul_smul] at h
  exact hnadj h

lemma avoidingGraph_pathSaturated (hT : T.IsAcyclic) :
    PathSaturated T (avoidingGraph (G := G) T u v) := by
  intro x y hxy p hp a ha b hb hab
  exact avoidingGraph_subpath T u v hT p (hxy.2 p hp) ha hb hab

lemma avoidingGraph_connected (hT : T.IsTree) (hA : PreservesAdj (G := G) T)
    (hne : u≠v) (hnadj : ¬T.Adj u v) : (avoidingGraph (G := G) T u v).Connected :=
  hT.connected.mono (le_avoidingGraph T u v hT.isAcyclic hA hne hnadj)

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
