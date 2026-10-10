import Mathlib
import OAI.Topology.ArtinGroups.Complexes.GeneratorVector

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A I K:Type*} (Q:ReversibleQuiver V A) [Field K] [Fintype A] [Fintype I] [DecidableEq V] [DecidableEq A]
omit [DecidableEq A] in
lemma generatorVector_pos_at (E:BasedComplex Q (K:=K) I) (i:I) :
    0<generatorVector Q E (E.placement i).color := by
  have : Nonempty {j:I // (E.placement j).color=(E.placement i).color}:=⟨⟨i,rfl⟩⟩
  change (0:ℝ)<(Nat.card {j:I // (E.placement j).color=(E.placement i).color}:ℝ)
  exact_mod_cast (Nat.card_pos (α:={j:I // (E.placement j).color=(E.placement i).color}))
end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
