import Mathlib
import OAI.Topology.ArtinGroups.Quivers.Path

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Path

variable {V A : Type*}

lemma length_cases (p : Path V A) : p.length = 0 ∨ p.length = 1 ∨ p.length = 2 := by
  rcases p with v | a | v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

end HarmonicArtin.ReversibleQuiver.Path

end OAI
