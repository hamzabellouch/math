import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace OAI

/-! Distance and path-support facts used by the tree acylindrification. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {V : Type} (T : SimpleGraph V)

lemma path_length_eq_dist (hT : T.IsAcyclic) {x y : V}
    (p : T.Walk x y) (hp : p.IsPath) : p.length=T.dist x y := by
  obtain ⟨q,hq,hl⟩ := p.reachable.exists_path_of_dist
  have he : p=q := congrArg Subtype.val
    (hT.subsingleton_path x y |>.elim ⟨p,hp⟩ ⟨q,hq⟩)
  rw [he]
  exact hl

lemma path_metric_additive (hT : T.IsAcyclic) {x y w : V}
    (p : T.Walk x y) (hp : p.IsPath) (hw : w∈p.support) :
    T.dist x y=T.dist x w+T.dist w y := by
  obtain ⟨q,r,hq,hr,he⟩ := hp.mem_support_iff_exists_append.mp hw
  rw [←path_length_eq_dist T hT p hp,he,SimpleGraph.Walk.length_append,
    path_length_eq_dist T hT q hq,path_length_eq_dist T hT r hr]

lemma path_support_subset_walk (hT : T.IsAcyclic) {x y : V}
    (p : T.Walk x y) (hp : p.IsPath) (q : T.Walk x y) : p.support⊆q.support := by
  classical
  have he : p=(q.toPath : T.Walk x y) := congrArg Subtype.val
    (hT.subsingleton_path x y |>.elim ⟨p,hp⟩ q.toPath)
  rw [he]
  exact q.support_toPath_subset_support

lemma path_support_subset_append (hT : T.IsAcyclic) {x y z : V}
    (p : T.Walk x z) (hp : p.IsPath) (q : T.Walk x y) (r : T.Walk y z)
    {w : V} (hw : w∈p.support) : w∈q.support ∨ w∈r.support := by
  have h := path_support_subset_walk T hT p hp (q.append r) hw
  exact (SimpleGraph.Walk.mem_support_append_iff q r).mp h

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
