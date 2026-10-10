import OAI.Topology.ArtinGroups.ParabolicIntersections.TreePeriodicPaths

namespace OAI

/-! Reflecting a segment at both ends constructs a tree translation. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (hA : PreservesAdj (G := G) T)

abbrev actPath (g : G) {x y : V} (p : T.Walk x y) : T.Walk (g • x) (g • y) :=
  p.map ⟨(g • ·),hA g⟩

lemma actPath_copy_length (g : G) {x y x' y' : V} (p : T.Walk x y)
    (hx : g • x=x') (hy : g • y=y') :
    ((actPath T hA g p).copy hx hy).length=p.length :=
  (SimpleGraph.Walk.length_copy _ _ _).trans (SimpleGraph.Walk.length_map _ _)

lemma actPath_copy_snd (g : G) {x y x' y' : V} (p : T.Walk x y)
    (hx : g • x=x') (hy : g • y=y') :
    ((actPath T hA g p).copy hx hy).snd=g • p.snd := by
  change ((actPath T hA g p).copy hx hy).getVert 1=g • p.getVert 1
  rw [SimpleGraph.Walk.getVert_copy,SimpleGraph.Walk.getVert_map]
  rfl

lemma actPath_copy_reverse_snd (g : G) {x y x' y' : V} (p : T.Walk x y)
    (hx : g • x=x') (hy : g • y=y') :
    ((actPath T hA g p).copy hx hy).reverse.snd=g • p.reverse.snd := by
  change ((actPath T hA g p).copy hx hy).reverse.getVert 1=g • p.reverse.getVert 1
  rw [SimpleGraph.Walk.reverse_copy,SimpleGraph.Walk.getVert_copy,SimpleGraph.Walk.reverse_map,
    SimpleGraph.Walk.getVert_map]
  rfl

lemma append_first {x y z : V} (p : T.Walk x y) (q : T.Walk y z)
    (hp : ¬p.Nil) : (p.append q).snd=p.snd := by
  cases p with
  | nil => exact (hp .nil).elim
  | cons h p => simp only [SimpleGraph.Walk.cons_append,SimpleGraph.Walk.snd_cons]

include hA in
theorem translation_segment (hT : T.IsAcyclic) {u v : V}
    (p : T.Walk u v) (hp : p.IsPath) (hpn : ¬p.Nil)
    (a b : G) (ha : a • u=u) (hb : b • v=v)
    (ha' : a • p.snd≠p.snd) (hb' : b • p.reverse.snd≠p.reverse.snd) :
    ∃ q : T.Walk u ((a*b) • u), q.IsPath ∧ ¬q.Nil ∧
      q.reverse.snd≠(a*b) • q.snd ∧ a • u∈q.support ∧ a • v∈q.support := by
  let l := (actPath T hA a p).copy ha rfl
  let r := (actPath T hA (a*b) p.reverse).copy (by rw [mul_smul,hb]) rfl
  have hl : l.IsPath := (SimpleGraph.Walk.isPath_copy _ _ _).mpr (hp.map (MulAction.toPerm a).injective)
  have hr : r.IsPath := (SimpleGraph.Walk.isPath_copy _ _ _).mpr (hp.reverse.map (MulAction.toPerm (a*b)).injective)
  have hlenl : l.length=p.length := by simp only [l,SimpleGraph.Walk.length_copy,SimpleGraph.Walk.length_map]
  have hlenr : r.length=p.length := by simp only [r,SimpleGraph.Walk.length_copy,SimpleGraph.Walk.length_map,SimpleGraph.Walk.length_reverse]
  have hn : 0 < p.length := Nat.pos_of_ne_zero (fun he => hpn (SimpleGraph.Walk.length_eq_zero_iff.mp he))
  have hln : ¬l.Nil := fun h => (by have he := h.length_eq_zero; omega)
  have hrn : ¬r.reverse.Nil := by
    intro h
    have he := h.length_eq_zero
    rw [SimpleGraph.Walk.length_reverse,hlenr] at he
    omega
  have hls : l.snd=a • p.snd := actPath_copy_snd T hA a p ha rfl
  have hlrs : l.reverse.snd=a • p.reverse.snd := actPath_copy_reverse_snd T hA a p ha rfl
  have hrs : r.snd=(a*b) • p.reverse.snd :=
    actPath_copy_snd T hA (a*b) p.reverse _ rfl
  have hrrs : r.reverse.snd=(a*b) • p.snd := by
    simpa only [SimpleGraph.Walk.reverse_reverse] using
      actPath_copy_reverse_snd T hA (a*b) p.reverse (by rw [mul_smul,hb]) rfl
  have hsep : l.reverse.snd≠r.snd := by
    rw [hlrs,hrs,mul_smul]
    exact fun he => hb' ((MulAction.toPerm a).injective he).symm
  have hq : (l.append r).IsPath := by
    have h := reverse_append_isPath T hT l.reverse r hl.reverse hr hsep
    simpa only [SimpleGraph.Walk.reverse_reverse] using h
  refine ⟨l.append r,hq,?_,?_,?_,?_⟩
  · intro h
    have he := h.length_eq_zero
    rw [SimpleGraph.Walk.length_append,hlenl,hlenr] at he
    omega
  · rw [SimpleGraph.Walk.reverse_append,append_first T r.reverse l.reverse hrn,
      append_first T l r hln,hls,hrrs]
    exact fun he => ha' ((MulAction.toPerm (a*b)).injective he).symm
  · rw [ha]
    exact (l.append r).start_mem_support
  · exact SimpleGraph.Walk.support_subset_support_append_left l r l.end_mem_support

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
