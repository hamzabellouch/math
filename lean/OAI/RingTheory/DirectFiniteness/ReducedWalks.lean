import OAI.RingTheory.DirectFiniteness.ReplacementPolygon

namespace OAI

universe u_1

noncomputable section
open scoped Classical
namespace SimpleGraph
open scoped _root_.SimpleGraph
open _root_.SimpleGraph _root_.OAI.SimpleGraph Walk
variable {V : Type u_1} {G : _root_.SimpleGraph V}

/-- A walk has no immediate backtracking when it has no closed subwalk
of length two. This formulation is hereditary under taking subwalks. -/
def Walk.Reduced {u v : V} (p : G.Walk u v) : Prop :=
  ∀ (w : V) (q : G.Walk w w), q.IsSubwalk p → q.length ≠ 2

lemma Walk.Reduced.of_isSubwalk {u v w x : V} {p : G.Walk u v} {q : G.Walk w x}
    (hp : _root_.OAI.SimpleGraph.Walk.Reduced p) (hq : q.IsSubwalk p) : _root_.OAI.SimpleGraph.Walk.Reduced q := by
  intro z r hr
  exact hp z r (hr.trans hq)

lemma Walk.Reduced.copy {u v u' v' : V} {p : G.Walk u v}
    (hp : _root_.OAI.SimpleGraph.Walk.Reduced p) (hu : u = u') (hv : v = v') : _root_.OAI.SimpleGraph.Walk.Reduced (p.copy hu hv) := by
  subst u' v'
  exact hp

/-- A nonempty closed walk with no immediate backtracking contains a cycle
no longer than itself. This is the girth fact used for facial boundaries. -/
theorem Walk.Reduced.exists_cycle {u : V} {p : G.Walk u u}
    (hp : _root_.OAI.SimpleGraph.Walk.Reduced p) (hne : ¬ p.Nil) :
    ∃ (v : V) (q : G.Walk v v), q.IsCycle ∧ q.length ≤ p.length := by
  classical
  generalize hn : p.length = n
  induction n using Nat.strong_induction_on generalizing u p with
  | h n ih =>
    by_cases ht : p.tail.IsPath
    · have hlen : 3 ≤ p.length := by
        have hpos : 0 < p.length := Nat.pos_of_ne_zero (fun h => hne (length_eq_zero_iff.mp h))
        have hnotone : p.length ≠ 1 := by
          intro h
          exact G.irrefl (p.adj_of_length_eq_one h)
        have hnottwo := hp u p p.isSubwalk_rfl
        omega
      exact ⟨u, p, (isCycle_iff_isPath_tail_and_le_length).mpr ⟨ht, hlen⟩, by omega⟩
    · rw [isPath_iff_isSubwalk_imp_nil] at ht
      push Not at ht
      obtain ⟨v, q, hsub, hq⟩ := ht
      have hqt : q.IsSubwalk p := hsub.trans p.isSubwalk_rfl.tail
      have hqred : _root_.OAI.SimpleGraph.Walk.Reduced q := hp.of_isSubwalk hqt
      have hlt : q.length < n := by
        have := length_le_of_isSubwalk hsub
        have htlen := p.length_tail
        have hpos : 0 < p.length := Nat.pos_of_ne_zero (fun h => hne (length_eq_zero_iff.mp h))
        omega
      obtain ⟨w, r, hr, hlen⟩ := ih q.length hlt hqred hq rfl
      exact ⟨w, r, hr, hlen.trans (by simpa only [hn] using length_le_of_isSubwalk hqt)⟩

lemma Walk.Reduced.egirth_le {u : V} {p : G.Walk u u}
    (hp : _root_.OAI.SimpleGraph.Walk.Reduced p) (hne : ¬ p.Nil) : G.egirth ≤ p.length := by
  obtain ⟨v, q, hq, hlen⟩ := hp.exists_cycle hne
  exact hq.egirth_le_length.trans (by exact_mod_cast hlen)

/-- The elementary vertex-index criterion for no immediate backtracking. -/
lemma Walk.reduced_of_getVert {u v : V} (p : G.Walk u v)
    (h : ∀ i, i + 2 ≤ p.length → p.getVert i ≠ p.getVert (i + 2)) : _root_.OAI.SimpleGraph.Walk.Reduced p := by
  intro w q hq hlen
  obtain ⟨r, s, rfl⟩ := hq
  have hi : r.length + 2 ≤ ((r.append q).append s).length := by
    simp only [length_append, hlen]
    omega
  have hstart : ((r.append q).append s).getVert r.length = w := by
    rw [getVert_append', ite_eq_left (by simp only [length_append]; omega),
      getVert_append', ite_eq_left le_rfl, getVert_length]
  have hend : ((r.append q).append s).getVert (r.length + 2) = w := by
    rw [getVert_append', ite_eq_left (by simp [hlen]),
      getVert_append, ite_eq_right (by omega)]
    simpa [hlen] using q.getVert_length
  exact h r.length hi (hstart.trans hend.symm)

end SimpleGraph

end

end OAI
