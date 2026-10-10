import Mathlib
import OAI.Topology.ArtinGroups.Quivers.CornerPath

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A : Type*} (Q : ReversibleQuiver V A)

structure SimpleEdge (α β : V) where
  arrow : A
  source : Q.source arrow = α
  target : Q.target arrow = β
  distinct : α ≠ β
  unique : ∀ a, Q.source a = α → Q.target a = β → a = arrow

namespace SimpleEdge

variable {α β : V} (e : SimpleEdge Q α β)

def reverse : SimpleEdge Q β α where
  arrow := Q.reverse e.arrow
  source := (Q.source_reverse _).trans e.target
  target := (Q.target_reverse _).trans e.source
  distinct := e.distinct.symm
  unique a hs ht := by
    have h := e.unique (Q.reverse a) ((Q.source_reverse _).trans ht)
      ((Q.target_reverse _).trans hs)
    have h' := congrArg Q.reverse h
    simpa only [Q.reverse_reverse] using h'

def corner : CornerPath Q α β := ⟨.inr (.inl e.arrow), e.source, e.target⟩

lemma corner_unique (p : CornerPath Q α β) : p = e.corner Q := by
  rcases p with ⟨v | a | v, hs, ht⟩
  · exact (e.distinct (hs.symm.trans ht)).elim
  · apply Subtype.ext
    change Sum.inr (Sum.inl a) = Sum.inr (Sum.inl e.arrow)
    exact congrArg (fun a => Sum.inr (Sum.inl a)) (e.unique a hs ht)
  · exact (e.distinct (hs.symm.trans ht)).elim

@[simp] lemma corner_val : (e.corner Q).val = .inr (.inl e.arrow) := rfl
@[simp] lemma reverse_arrow : (e.reverse Q).arrow = Q.reverse e.arrow := rfl

end SimpleEdge
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
