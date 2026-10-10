import Mathlib
import OAI.Topology.ArtinGroups.Complexes.LevelArrayMinimalApply

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type} {K:Type*} [Field K] [Fintype V] [Fintype A]
  (Q:ReversibleQuiver V A) [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma classLevelArray_below (x:FiniteHomotopyClass Q (K:=K)) (k l:ℤ)
    (hx:ClassLowerBound Q k x) (hl:l<k) (α:V) : classLevelArray Q x (α,l)=0 := by
  rw [classLevelArray_minimal_apply]
  let :IsEmpty {i:(minimalClassModel Q x).Index //
      ((minimalClassModel Q x).complex.placement i).color=α ∧
      ((minimalClassModel Q x).complex.placement i).level=l}:=⟨by
    rintro ⟨i,hi,he⟩
    have hh:=hx i
    omega⟩
  exact Nat.card_of_isEmpty

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
