import Mathlib
import OAI.Topology.ArtinGroups.Complexes.LevelArrayMinimalApply

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type} {K:Type*} [Field K] [Fintype V] [Fintype A]
  (Q:ReversibleQuiver V A) [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma classGeneratorArray_zero_of_level (x:FiniteHomotopyClass Q (K:=K))
    (p:GeneratorPlacement V) (h:classLevelArray Q x (p.color,p.level)=0) :
    classGeneratorArray Q x p=0 := by
  rw [classLevelArray_minimal_apply] at h
  rw [← minimalClassModel_class Q x,
    classGeneratorArray_of_minimal Q _ (minimalClassModel_minimal Q x),generatorArray_apply]
  let E:=minimalClassModel Q x
  change Nat.card {i:E.Index // E.complex.placement i=p}=0
  have : IsEmpty {i:E.Index // E.complex.placement i=p}:=⟨by
    rintro ⟨i,hi⟩
    have : Nonempty {j:E.Index // (E.complex.placement j).color=p.color ∧
      (E.complex.placement j).level=p.level}:=⟨⟨i,by rw [hi]; exact ⟨rfl,rfl⟩⟩⟩
    have hp:0<Nat.card {j:E.Index // (E.complex.placement j).color=p.color ∧
      (E.complex.placement j).level=p.level}:=Nat.card_pos
    exact Nat.ne_of_gt hp h⟩
  exact Nat.card_of_isEmpty

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
