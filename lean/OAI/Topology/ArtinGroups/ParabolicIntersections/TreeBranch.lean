import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeFixedPaths

namespace OAI

/-! Reflecting a segment at an endpoint and extending it along a new edge. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (hT : T.IsAcyclic) (hA : PreservesAdj (G := G) T)
include hT hA

lemma moved_first_vertex_ne_endpoint {u v : V} (p : T.Walk v u) (hp : p.IsPath)
    (g : G) (hg : g • v=v) (hw : g • p.snd≠p.snd) : g • u≠u := by
  intro hu
  exact hw (fixes_path T hT hA p hp g hg hu 1)

/-- Reflecting a path across its initial vertex intersects its endpoint
stabilizer with a conjugate, and still gives an endpoint stabilizer. -/
theorem reflected_pair (u v : V) (p : T.Walk v u) (hp : p.IsPath)
    (g : G) (hg : g • v=v) (hw : g • p.snd≠p.snd) :
    pairStabilizer (G := G) u (g • u)=pairStabilizer (G := G) u v ⊓
      conjugate g (pairStabilizer (G := G) u v) := by
  let q := (p.map (translate T hA g)).copy hg rfl
  have hq : q.IsPath := by
    apply (SimpleGraph.Walk.isPath_copy _ _ _).mpr
    exact hp.map (MulAction.toPerm g).injective
  have hs : p.snd≠q.snd := by
    change p.getVert 1≠q.getVert 1
    have hqv : q.getVert 1=g • p.getVert 1 := by
      calc
        q.getVert 1 = (p.map (translate T hA g)).getVert 1 :=
          SimpleGraph.Walk.getVert_copy _ 1 hg rfl
        _ = g • p.getVert 1 := SimpleGraph.Walk.getVert_map _ _ 1
    rw [hqv]
    exact hw.symm
  have hr := reverse_append_isPath T hT p q hp hq hs
  have hv : v∈(p.reverse.append q).support := by
    rw [SimpleGraph.Walk.support_append_eq_support_dropLast_append]
    exact List.mem_append_right _ q.start_mem_support
  have hfix := pairStabilizer_le_at_path T hT hA (p.reverse.append q) hr hv
  rw [←pairStabilizer_smul,hg]
  apply le_antisymm
  · intro a ha
    exact ⟨⟨ha.1,hfix ha⟩,ha.2,hfix ha⟩
  · intro a ha
    exact ⟨ha.1.1,ha.2.1⟩

omit hA in
/-- An edge leaving the initial direction of a path extends the path. -/
lemma reverse_concat_isPath {u v w : V} (p : T.Walk v u) (hp : p.IsPath)
    (hadj : T.Adj v w) (hw : w≠p.snd) : (p.reverse.concat hadj).IsPath := by
  apply hp.reverse.concat
  · intro hm
    have hm' : w∈p.support := by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hm
    exact hw (hT.eq_snd_of_adj_start hp hadj hm')

/-- If the old stabilizer fixes the added vertex, extension preserves it. -/
theorem extended_pair (u v w : V) (p : T.Walk v u) (hp : p.IsPath)
    (hadj : T.Adj v w) (hw : w≠p.snd)
    (hfix : pairStabilizer (G := G) u v≤MulAction.stabilizer G w) :
    pairStabilizer (G := G) u w=pairStabilizer (G := G) u v := by
  have hr := reverse_concat_isPath T hT p hp hadj hw
  have hv : v∈(p.reverse.concat hadj).support := by
    rw [SimpleGraph.Walk.support_concat]
    exact List.mem_append_left _ p.reverse.end_mem_support
  have hfix' := pairStabilizer_le_at_path T hT hA _ hr hv
  apply le_antisymm
  · intro a ha
    exact ⟨ha.1,hfix' ha⟩
  · intro a ha
    exact ⟨ha.1,hfix ha⟩

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
