import OAI.Topology.ArtinGroups.ParabolicIntersections.DynamicsDefinitions
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace OAI

/-! Irreducibility is connectedness of the noncommutation graph. -/
namespace HarmonicArtin.ParabolicIntersections
variable {S : Type} (M : CoxeterMatrix S)

def noncommutingGraph : SimpleGraph S where
  Adj a b := a≠b ∧ M a b≠2
  symm := ⟨by
    intro a b h
    exact ⟨h.1.symm,fun he => h.2 ((M.symmetric a b).trans he)⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

lemma noncommuting_reachable (hIrred : IsIrreducible M) (s t : S) :
    (noncommutingGraph M).Reachable s t := by
  by_contra ht
  let X : Set S := {v | (noncommutingGraph M).Reachable s v}
  obtain ⟨a,ha,b,hb,hm⟩ := hIrred X ⟨s,SimpleGraph.Reachable.rfl⟩ ⟨t,ht⟩
  have hab : a≠b := fun he => hb (he ▸ ha)
  exact hb (ha.trans (show (noncommutingGraph M).Adj a b from ⟨hab,hm⟩).reachable)

/-- A list with a term outside a set has an initial segment whose last
term is the first outside term. -/
lemma list_first_outside (C : Set S) (l : List S) (h : ∃ s∈l,s∉C) :
    ∃ u s v, l=u++s::v ∧ (∀ t∈u,t∈C) ∧ s∉C := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    by_cases ha : a∈C
    · have hl : ∃ s∈l,s∉C := by
        obtain ⟨s,hs,hsc⟩ := h
        rcases List.mem_cons.mp hs with rfl|hs
        · exact (hsc ha).elim
        · exact ⟨s,hs,hsc⟩
      obtain ⟨u,s,v,he,hu,hs⟩ := ih hl
      refine ⟨a::u,s,v,?_,?_,hs⟩
      · rw [he]
        rfl
      · intro t ht
        rcases List.mem_cons.mp ht with rfl|ht
        · exact ha
        · exact hu t ht
    · exact ⟨[],a,l,rfl,by simp,ha⟩

end HarmonicArtin.ParabolicIntersections

end OAI
