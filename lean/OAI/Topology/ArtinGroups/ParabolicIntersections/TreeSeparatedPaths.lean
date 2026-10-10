import OAI.Topology.ArtinGroups.ParabolicIntersections.TreePaths
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreePathMetric

namespace OAI

/-! Distances between different branches of a tree. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} (T : SimpleGraph V)

lemma reverse_append_of_common {b x y : V} (s : T.Walk b x) (t : T.Walk b y)
    (hs : s.IsPath) (ht : t.IsPath)
    (hc : ∀ w∈s.support,w∈t.support → w=b) : (s.reverse.append t).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [SimpleGraph.Walk.support_append_eq_support_dropLast_append]
  apply List.Nodup.append (hs.reverse.support_nodup.sublist (List.dropLast_sublist _)) ht.support_nodup
  intro w hw ht'
  have hs' : w∈s.support := by
    simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using List.dropLast_subset _ hw
  have he := hc w hs' ht'
  have hn := hs.reverse.support_nodup.rel_dropLast_getLast hw
  exact hn (by simpa only [SimpleGraph.Walk.getLast_support] using he)

lemma dist_sum_of_branches (hT : T.IsAcyclic) {b x y a c : V}
    (s : T.Walk b x) (t : T.Walk b y) (hs : s.IsPath) (ht : t.IsPath)
    (hc : ∀ w∈s.support,w∈t.support → w=b)
    (ha : a∈s.support) (hc' : c∈t.support) :
    T.dist b a+T.dist b c=T.dist a c := by
  let p := s.takeUntil a ha
  let q := t.takeUntil c hc'
  have hp : p.IsPath := hs.takeUntil ha
  have hq : q.IsPath := ht.takeUntil hc'
  have hpq : (p.reverse.append q).IsPath :=
    reverse_append_of_common T p q hp hq (fun w hw hw' =>
      hc w (s.support_takeUntil_subset_support ha hw) (t.support_takeUntil_subset_support hc' hw'))
  have hb : b∈(p.reverse.append q).support :=
    SimpleGraph.Walk.support_subset_support_append_right _ _ q.start_mem_support
  have he := path_metric_additive T hT _ hpq hb
  rw [T.dist_comm (u := a) (v := b)] at he
  exact he.symm

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
