import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeSegmentBallCount
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeSeparatedPaths
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeTripod
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeAvoidingGraph
import OAI.Topology.ArtinGroups.ParabolicIntersections.GraphMetric

namespace OAI

/-! Uniform counts of free segment translates along shortcut paths. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (u v : V)

lemma segmentOccurrences_branches (hT : T.IsTree) (hA : PreservesAdj (G := G) T)
    {b x y : V} (s : T.Walk b x) (t : T.Walk b y)
    (hs : s.IsPath) (ht : t.IsPath)
    (hc : ∀ w∈s.support,w∈t.support → w=b) :
    segmentOccurrences (G := G) u v T (s.reverse.append t) ⊆
      segmentOccurrences u v T s ∪ segmentOccurrences u v T t ∪
        localSegmentOccurrences T u v (s.reverse.append t) b (T.dist u v) := by
  intro g hg
  have hgu := (SimpleGraph.Walk.mem_support_append_iff s.reverse t).mp hg.1
  have hgv := (SimpleGraph.Walk.mem_support_append_iff s.reverse t).mp hg.2
  simp only [SimpleGraph.Walk.support_reverse,List.mem_reverse] at hgu hgv
  have hd := graph_action_dist T hT.connected hA g u v
  rcases hgu with hgu|hgu <;> rcases hgv with hgv|hgv
  · exact Or.inl (Or.inl ⟨hgu,hgv⟩)
  · right
    have he := dist_sum_of_branches T hT.isAcyclic s t hs ht hc hgu hgv
    exact ⟨⟨hg.1,by omega⟩,⟨hg.2,by omega⟩⟩
  · right
    have he := dist_sum_of_branches T hT.isAcyclic s t hs ht hc hgv hgu
    rw [T.dist_comm (u := g • v) (v := g • u)] at he
    exact ⟨⟨hg.1,by omega⟩,⟨hg.2,by omega⟩⟩
  · exact Or.inl (Or.inr ⟨hgu,hgv⟩)

lemma branch_support_common (hT : T.IsAcyclic) {b x y : V}
    (s : T.Walk b x) (t : T.Walk b y) (hs : s.IsPath) (ht : t.IsPath)
    (hd : s.Nil ∨ t.Nil ∨ s.snd≠t.snd) :
    ∀ w∈s.support,w∈t.support → w=b := by
  intro w hw hw'
  rcases hd with hn|hn|hne
  · cases hn
    simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hw
  · cases hn
    simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hw'
  · exact common_support_eq_start T hT s t hs ht hne hw hw'

/-- A shortcut walk of length `n` crosses at most `n (2L+1)^2`
translates of a free length-`L` segment, independently of vertex valences. -/
theorem segmentOccurrences_bound (hT : T.IsTree) (hA : PreservesAdj (G := G) T)
    (hfree : pairStabilizer (G := G) u v=⊥) (hne : u≠v)
    {x y : V} (q : (avoidingGraph (G := G) T u v).Walk x y)
    (p : T.Walk x y) (hp : p.IsPath) :
    (segmentOccurrences (G := G) u v T p).ncard ≤ q.length*(2*T.dist u v+1)^2 := by
  induction q with
  | @nil x =>
    have he : p=.nil := congrArg Subtype.val
      (hT.isAcyclic.subsingleton_path _ _ |>.elim ⟨p,hp⟩ ⟨.nil,by simp⟩)
    rw [he]
    have hempty : segmentOccurrences (G := G) u v T (.nil : T.Walk x x)=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro g hg
      have hgu : g • u=x := by simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hg.1
      have hgv : g • v=x := by simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hg.2
      exact hne ((MulAction.toPerm g).injective (hgu.trans hgv.symm))
    rw [hempty]
    simp
  | @cons x z y hxz q ih =>
    obtain ⟨r,hr⟩ := hT.connected.exists_isPath x z
    obtain ⟨w,hw⟩ := hT.connected.exists_isPath z y
    obtain ⟨b,a,s,t,hrs,hwt,hd⟩ := walk_common_prefix T r.reverse w
    have hs : s.IsPath := (hrs ▸ hr.reverse).of_append_right
    have ht : t.IsPath := (hwt ▸ hw).of_append_right
    have hc := branch_support_common T hT.isAcyclic s t hs ht hd
    have hst := reverse_append_of_common T s t hs ht hc
    have he : p=s.reverse.append t := congrArg Subtype.val
      (hT.isAcyclic.subsingleton_path _ _ |>.elim ⟨p,hp⟩ ⟨_,hst⟩)
    have hno : ¬ContainsSegment (G := G) u v T r := hxz.2 r hr
    have hsub : segmentOccurrences (G := G) u v T p ⊆
        segmentOccurrences u v T w ∪ localSegmentOccurrences T u v p b (T.dist u v) := by
      intro g hg
      rw [he] at hg
      rcases segmentOccurrences_branches T u v hT hA s t hs ht hc hg with (hgs|hgt)|hgl
      · exfalso
        apply hno
        have hsr : s.support⊆r.reverse.support := by
          rw [hrs]
          exact SimpleGraph.Walk.support_subset_support_append_right a s
        refine ⟨g,?_,?_⟩
        · simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hsr hgs.1
        · simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hsr hgs.2
      · left
        have htw : t.support⊆w.support := by
          rw [hwt]
          exact SimpleGraph.Walk.support_subset_support_append_right a t
        exact ⟨htw hgt.1,htw hgt.2⟩
      · exact Or.inr (he ▸ hgl)
    have hb : b∈p.support := by
      rw [he]
      exact SimpleGraph.Walk.support_subset_support_append_right s.reverse t t.start_mem_support
    have hlocal := localSegmentOccurrences_bound T u v hT hfree p hp hb (T.dist u v)
    have hn := ih w hw
    calc
      (segmentOccurrences (G := G) u v T p).ncard ≤
          (segmentOccurrences u v T w ∪ localSegmentOccurrences T u v p b (T.dist u v)).ncard :=
        Set.ncard_le_ncard hsub ((segmentOccurrences_finite hfree T w).union hlocal.1)
      _ ≤ (segmentOccurrences (G := G) u v T w).ncard+
          (localSegmentOccurrences T u v p b (T.dist u v)).ncard := Set.ncard_union_le _ _
      _ ≤ q.length*(2*T.dist u v+1)^2+(2*T.dist u v+1)^2 := Nat.add_le_add hn hlocal.2
      _ = (q.cons hxz).length*(2*T.dist u v+1)^2 := by
        simp only [SimpleGraph.Walk.length_cons,Nat.add_mul,one_mul]

theorem segmentOccurrences_bound_dist (hT : T.IsTree) (hA : PreservesAdj (G := G) T)
    (hfree : pairStabilizer (G := G) u v=⊥) (hne : u≠v) (hnadj : ¬T.Adj u v)
    {x y : V} (p : T.Walk x y) (hp : p.IsPath) :
    (segmentOccurrences (G := G) u v T p).ncard ≤
      (avoidingGraph (G := G) T u v).dist x y*(2*T.dist u v+1)^2 := by
  obtain ⟨q,hq⟩ := (avoidingGraph_connected T u v hT hA hne hnadj).exists_walk_length_eq_dist x y
  simpa only [hq] using segmentOccurrences_bound T u v hT hA hfree hne q p hp

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
