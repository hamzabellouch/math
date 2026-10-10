import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeConvex

namespace OAI

/-! A group preserving both sides of a bridge fixes its endpoints. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V)

lemma snd_append_of_not_nil {u v w : V} (p : T.Walk u v) (q : T.Walk v w)
    (hp : ¬p.Nil) : (p.append q).snd=p.snd := by
  cases p with
  | nil => exact (hp .nil).elim
  | cons h p => simp only [SimpleGraph.Walk.cons_append,SimpleGraph.Walk.snd_cons]

/-- The endpoint-exit condition identifies a bridge between two convex sets.
Comparing its length with a translated path forces both endpoints to be fixed. -/
theorem fixes_bridge (hT : T.IsTree) (hA : PreservesAdj (G := G) T)
    {U W : Set V} (hU : PathClosed T U) (hW : PathClosed T W)
    {u v : V} (hu : u∈U) (hv : v∈W) (p : T.Walk u v) (hp : p.IsPath)
    (hpu : p.snd∉U) (hpv : p.reverse.snd∉W)
    (g : G) (hgU : ∀ x∈U,g • x∈U) (hgW : ∀ x∈W,g • x∈W) :
    g • u=u ∧ g • v=v := by
  obtain ⟨q,hq⟩ := hT.connected.exists_isPath u (g • u)
  obtain ⟨r,hr⟩ := hT.connected.exists_isPath v (g • v)
  have hqs : q.snd∈U := hU hu (hgU u hu) q hq _ (q.getVert_mem_support 1)
  have hrs : r.snd∈W := hW hv (hgW v hv) r hr _ (r.getVert_mem_support 1)
  have hqp : (q.reverse.append p).IsPath :=
    reverse_append_isPath T hT.isAcyclic q p hq hp (fun he => hpu (he ▸ hqs))
  have hn : ¬p.reverse.Nil := by
    intro hn
    have hnil : p.Nil := by
      apply SimpleGraph.Walk.length_eq_zero_iff.mp
      simpa only [SimpleGraph.Walk.length_reverse] using hn.length_eq_zero
    have hs : p.snd=u := by
      cases hnil
      exact SimpleGraph.Walk.getVert_nil u
    exact hpu (hs.symm ▸ hu)
  have hs : (q.reverse.append p).reverse.snd=p.reverse.snd := by
    rw [SimpleGraph.Walk.reverse_append,SimpleGraph.Walk.reverse_reverse]
    exact snd_append_of_not_nil T p.reverse q hn
  have hfull : ((q.reverse.append p).append r).IsPath := by
    have h := reverse_append_isPath T hT.isAcyclic (q.reverse.append p).reverse r
      hqp.reverse hr (fun he => hpv (hs ▸ he.symm ▸ hrs))
    simpa only [SimpleGraph.Walk.reverse_reverse] using h
  have he : (q.reverse.append p).append r=p.map (translate T hA g) :=
    congrArg Subtype.val (hT.isAcyclic.subsingleton_path (g • u) (g • v) |>.elim
      ⟨_,hfull⟩ ⟨_,hp.map (MulAction.toPerm g).injective⟩)
  have hl := congrArg SimpleGraph.Walk.length he
  simp only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_reverse] at hl
  have hm := SimpleGraph.Walk.length_map (translate T hA g) p
  have hl' : q.length+p.length+r.length=p.length := hl.trans hm
  have hq0 : q.length=0 := by omega
  have hr0 : r.length=0 := by omega
  exact ⟨(SimpleGraph.Walk.eq_of_length_eq_zero hq0).symm,
    (SimpleGraph.Walk.eq_of_length_eq_zero hr0).symm⟩

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
