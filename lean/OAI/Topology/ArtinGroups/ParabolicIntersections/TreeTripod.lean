import OAI.Topology.ArtinGroups.ParabolicIntersections.TreePaths
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreePathMetric

namespace OAI

/-! Common prefixes and tripods for paths in a tree. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} (T : SimpleGraph V)

lemma walk_common_prefix {x y z : V} (p : T.Walk x y) (q : T.Walk x z) :
    ∃ b, ∃ (r : T.Walk x b) (s : T.Walk b y) (t : T.Walk b z),
      p=r.append s ∧ q=r.append t ∧ (s.Nil ∨ t.Nil ∨ s.snd≠t.snd) := by
  classical
  induction p generalizing z with
  | nil => exact ⟨_,.nil,.nil,q,by simp,by simp,Or.inl .nil⟩
  | @cons x v y h p ih =>
    cases q with
    | nil => exact ⟨x,.nil,p.cons h,.nil,by simp,by simp,Or.inr (Or.inl .nil)⟩
    | @cons _ w z h' q =>
      by_cases he : v=w
      · subst w
        obtain ⟨b,r,s,t,hp,hq,hd⟩ := ih q
        refine ⟨b,r.cons h,s,t,?_,?_,hd⟩
        · rw [hp]
          rfl
        · rw [hq]
          rfl
      · refine ⟨x,.nil,p.cons h,q.cons h',by simp,by simp,Or.inr (Or.inr ?_)⟩
        simpa only [SimpleGraph.Walk.snd_cons] using he

lemma tree_tripod (hT : T.IsAcyclic) {x y z : V}
    (p : T.Walk x y) (q : T.Walk x z) (r : T.Walk y z)
    (hp : p.IsPath) (hq : q.IsPath) (hr : r.IsPath) :
    ∃ b,b∈p.support ∧ b∈q.support ∧ b∈r.support := by
  obtain ⟨b,a,s,t,hp',hq',hd⟩ := walk_common_prefix T p q
  have hs : s.IsPath := (hp' ▸ hp).of_append_right
  have ht : t.IsPath := (hq' ▸ hq).of_append_right
  have hst : (s.reverse.append t).IsPath := by
    rcases hd with hn|hn|hne
    · cases hn
      simpa using ht
    · cases hn
      simpa using hs.reverse
    · exact reverse_append_isPath T hT s t hs ht hne
  have he : r=s.reverse.append t := congrArg Subtype.val
    (hT.subsingleton_path y z |>.elim ⟨r,hr⟩ ⟨_,hst⟩)
  refine ⟨b,?_,?_,?_⟩
  · rw [hp']
    exact SimpleGraph.Walk.support_subset_support_append_right a s s.start_mem_support
  · rw [hq']
    exact SimpleGraph.Walk.support_subset_support_append_right a t t.start_mem_support
  · rw [he]
    exact SimpleGraph.Walk.support_subset_support_append_right s.reverse t t.start_mem_support

lemma prefixes_comparable {x y a b : V} (p : T.Walk x y)
    (ha : a∈p.support) (hb : b∈p.support) :
    a∈(p.takeUntil b hb).support ∨ b∈(p.takeUntil a ha).support := by
  classical
  rcases le_total (p.takeUntil a ha).length (p.takeUntil b hb).length with h|h
  · left
    have he : (p.takeUntil b hb).getVert (p.takeUntil a ha).length=a := by
      rw [p.getVert_takeUntil hb h,p.getVert_length_takeUntil ha]
    exact he ▸ (p.takeUntil b hb).getVert_mem_support _
  · right
    have he : (p.takeUntil a ha).getVert (p.takeUntil b hb).length=b := by
      rw [p.getVert_takeUntil ha h,p.getVert_length_takeUntil hb]
    exact he ▸ (p.takeUntil a ha).getVert_mem_support _

lemma common_support_in_prefix (hT : T.IsAcyclic) {x b y z w : V}
    (a : T.Walk x b) (s : T.Walk b y) (t : T.Walk b z)
    (hs : s.IsPath) (ht : t.IsPath) (hd : s.Nil ∨ t.Nil ∨ s.snd≠t.snd)
    (hw : w∈(a.append s).support) (hw' : w∈(a.append t).support) :
    w∈a.support := by
  rcases hd with hn|hn|hne
  · cases hn
    simpa only [SimpleGraph.Walk.append_nil] using hw
  · cases hn
    simpa only [SimpleGraph.Walk.append_nil] using hw'
  · by_contra hwa
    have hws := ((SimpleGraph.Walk.mem_support_append_iff a s).mp hw).resolve_left hwa
    have hwt := ((SimpleGraph.Walk.mem_support_append_iff a t).mp hw').resolve_left hwa
    have he := common_support_eq_start T hT s t hs ht hne hws hwt
    exact hwa (he.symm ▸ a.end_mem_support)

/-- The common prefix contains every common vertex of the two paths. -/
lemma tree_branchpoint (hT : T.IsAcyclic) {x y z : V}
    (p : T.Walk x y) (q : T.Walk x z) (r : T.Walk y z)
    (hp : p.IsPath) (hq : q.IsPath) (hr : r.IsPath) :
    ∃ b, ∃ hbp : b∈p.support,
      b∈q.support ∧ b∈r.support ∧
        ∀ w∈p.support,w∈q.support → w∈(p.takeUntil b hbp).support := by
  classical
  obtain ⟨b,a,s,t,hp',hq',hd⟩ := walk_common_prefix T p q
  have ha : a.IsPath := (hp' ▸ hp).of_append_left
  have hs : s.IsPath := (hp' ▸ hp).of_append_right
  have ht : t.IsPath := (hq' ▸ hq).of_append_right
  have hbp : b∈p.support := by
    rw [hp']
    exact SimpleGraph.Walk.support_subset_support_append_left a s a.end_mem_support
  have hbq : b∈q.support := by
    rw [hq']
    exact SimpleGraph.Walk.support_subset_support_append_left a t a.end_mem_support
  have hst : (s.reverse.append t).IsPath := by
    rcases hd with hn|hn|hne
    · cases hn
      simpa using ht
    · cases hn
      simpa using hs.reverse
    · exact reverse_append_isPath T hT s t hs ht hne
  have he : r=s.reverse.append t := congrArg Subtype.val
    (hT.subsingleton_path y z |>.elim ⟨r,hr⟩ ⟨_,hst⟩)
  have hbr : b∈r.support := by
    rw [he]
    exact SimpleGraph.Walk.support_subset_support_append_right s.reverse t t.start_mem_support
  refine ⟨b,hbp,hbq,hbr,?_⟩
  have htake : p.takeUntil b hbp=a := congrArg Subtype.val
    (hT.subsingleton_path x b |>.elim ⟨_,hp.takeUntil hbp⟩ ⟨a,ha⟩)
  intro w hwp hwq
  rw [htake]
  apply common_support_in_prefix T hT a s t hs ht hd
  · rwa [←hp']
  · rwa [←hq']

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
