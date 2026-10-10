import Mathlib
import OAI.Topology.ArtinGroups.Complexes.LevelArrayMinimalApply

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma finiteFamily_level_support {R:Type} [Finite R]
    (x:R→FiniteHomotopyClass Q (K:=K)) :
    {k:ℤ | ∃ r α,classLevelArray Q (x r) (α,k)≠0}.Finite := by
  let F : Set ℤ := Set.range (fun z:Σ r:R,(minimalClassModel Q (x r)).Index=>
    ((minimalClassModel Q (x z.1)).complex.placement z.2).level)
  have hF:F.Finite:=Set.finite_range _
  apply hF.subset
  rintro k ⟨r,α,hk⟩
  rw [classLevelArray_minimal_apply] at hk
  have hn:Nonempty {i:(minimalClassModel Q (x r)).Index //
      ((minimalClassModel Q (x r)).complex.placement i).color=α ∧
      ((minimalClassModel Q (x r)).complex.placement i).level=k} :=
    Nat.card_ne_zero.mp hk |>.1
  obtain ⟨i⟩:=hn
  exact ⟨⟨r,i.val⟩,i.property.2⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
