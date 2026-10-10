import OAI.Topology.ArtinGroups.ParabolicIntersections.TreePathMetric

namespace OAI

/-! Tree paths are approximate geodesics in a graph with convex shortcuts. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {V : Type} (T H : SimpleGraph V)

/-- Every path shortcut includes all shorter shortcuts along the same tree path. -/
def PathSaturated : Prop := ∀ ⦃x y⦄, H.Adj x y →
  ∀ p : T.Walk x y,p.IsPath → ∀ a∈p.support,∀ b∈p.support,a≠b → H.Adj a b

lemma shortcut_adj_split (hS : PathSaturated T H) {x y w : V}
    (hxy : H.Adj x y) (p : T.Walk x y) (hp : p.IsPath) (hw : w∈p.support) :
    ∃ (q : H.Walk x w) (r : H.Walk w y),q.length≤1 ∧ r.length≤1 := by
  have hx : ∃ q : H.Walk x w,q.length≤1 := by
    by_cases he : x=w
    · subst w
      exact ⟨.nil,by simp⟩
    · exact ⟨(hS hxy p hp x p.start_mem_support w hw he).toWalk,by simp⟩
  have hy : ∃ r : H.Walk w y,r.length≤1 := by
    by_cases he : w=y
    · subst w
      exact ⟨.nil,by simp⟩
    · exact ⟨(hS hxy p hp w hw y p.end_mem_support he).toWalk,by simp⟩
  obtain ⟨q,hq⟩ := hx
  obtain ⟨r,hr⟩ := hy
  exact ⟨q,r,hq,hr⟩

lemma shortcut_path_split (hT : T.IsTree) (hS : PathSaturated T H)
    {x y : V} (q : H.Walk x y) (p : T.Walk x y) (hp : p.IsPath)
    {w : V} (hw : w∈p.support) :
    ∃ (a : H.Walk x w) (b : H.Walk w y),a.length+b.length≤q.length+1 := by
  induction q with
  | nil =>
    have he : p=.nil := congrArg Subtype.val
      (hT.isAcyclic.subsingleton_path _ _ |>.elim ⟨p,hp⟩ ⟨.nil,by simp⟩)
    rw [he] at hw
    simp only [SimpleGraph.Walk.support_nil,List.mem_singleton] at hw
    subst w
    exact ⟨.nil,.nil,by simp⟩
  | @cons x z y hxz q ih =>
    obtain ⟨r,hr⟩ := hT.connected.exists_isPath x z
    obtain ⟨s,hs⟩ := hT.connected.exists_isPath z y
    rcases path_support_subset_append T hT.isAcyclic p hp r s hw with hw|hw
    · obtain ⟨a,b,ha,hb⟩ := shortcut_adj_split T H hS hxz r hr hw
      refine ⟨a,b.append q,?_⟩
      simp only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_cons]
      omega
    · obtain ⟨a,b,hab⟩ := ih s hs hw
      refine ⟨a.cons hxz,b,?_⟩
      simp only [SimpleGraph.Walk.length_cons]
      omega

/-- A tree-path point splits distance in the shortcut graph up to one edge. -/
theorem shortcut_dist_split (hT : T.IsTree) (hH : H.Connected)
    (hS : PathSaturated T H) {x y w : V}
    (p : T.Walk x y) (hp : p.IsPath) (hw : w∈p.support) :
    H.dist x w+H.dist w y≤H.dist x y+1 := by
  obtain ⟨q,hq⟩ := hH.exists_walk_length_eq_dist x y
  obtain ⟨a,b,hab⟩ := shortcut_path_split T H hT hS q p hp hw
  calc
    H.dist x w+H.dist w y ≤ a.length+b.length :=
      Nat.add_le_add (H.dist_le a) (H.dist_le b)
    _ ≤ q.length+1 := hab
    _ = H.dist x y+1 := by rw [hq]

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
