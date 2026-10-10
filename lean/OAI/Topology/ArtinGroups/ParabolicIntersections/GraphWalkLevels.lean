import OAI.Topology.ArtinGroups.ParabolicIntersections.GraphMetric

namespace OAI

/-! Integer distance levels along a graph walk. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {V : Type} (H : SimpleGraph V)

lemma walk_exists_dist_level (hH : H.Connected) (o : V) {x y : V}
    (p : H.Walk x y) (k : ℕ) (hx : H.dist o x ≤ k) (hy : k ≤ H.dist o y) :
    ∃ w∈p.support,H.dist o w=k := by
  induction p with
  | nil => exact ⟨_,by simp,Nat.le_antisymm hx hy⟩
  | @cons x z y hxz p ih =>
    by_cases he : H.dist o x=k
    · exact ⟨x,by simp,he⟩
    · have hz : H.dist o z ≤ k := by
        have ht := hH.dist_triangle (u := o) (v := x) (w := z)
        have hd := H.dist_eq_one_iff_adj.mpr hxz
        omega
      obtain ⟨w,hw,hd⟩ := ih hz hy
      exact ⟨w,by simp only [SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr hw,hd⟩

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
