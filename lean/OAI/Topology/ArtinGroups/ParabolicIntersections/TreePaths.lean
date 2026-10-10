import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace OAI

/-! Elementary path geometry in a simplicial tree. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} (T : SimpleGraph V)

/-- Paths starting in different directions meet only at their initial vertex. -/
theorem common_support_eq_start (hT : T.IsAcyclic) {u v w x : V}
    (p : T.Walk u v) (q : T.Walk u w) (hp : p.IsPath) (hq : q.IsPath)
    (hs : p.snd≠q.snd) (hxp : x∈p.support) (hxq : x∈q.support) : x=u := by
  by_contra hxu
  have he : p.takeUntil x hxp=q.takeUntil x hxq :=
    congrArg Subtype.val (hT.subsingleton_path u x |>.elim
      ⟨_,hp.takeUntil hxp⟩ ⟨_,hq.takeUntil hxq⟩)
  have hh := congrArg (fun r : T.Walk u x => r.snd) he
  rw [SimpleGraph.Walk.snd_takeUntil hxu,SimpleGraph.Walk.snd_takeUntil hxu] at hh
  exact hs hh

/-- Two paths in different directions form a single longer path. -/
theorem reverse_append_isPath (hT : T.IsAcyclic) {u v w : V}
    (p : T.Walk u v) (q : T.Walk u w) (hp : p.IsPath) (hq : q.IsPath)
    (hs : p.snd≠q.snd) : (p.reverse.append q).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [SimpleGraph.Walk.support_append_eq_support_dropLast_append]
  apply List.Nodup.append (hp.reverse.support_nodup.sublist (List.dropLast_sublist _)) hq.support_nodup
  intro x hxp hxq
  have hxp' : x∈p.support := by
    simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using List.dropLast_subset _ hxp
  have he := common_support_eq_start T hT p q hp hq hs hxp' hxq
  have hn := hp.reverse.support_nodup.rel_dropLast_getLast hxp
  exact hn (by simpa only [SimpleGraph.Walk.getLast_support] using he)

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
