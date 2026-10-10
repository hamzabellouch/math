import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PacketPermReindex
import OAI.Topology.ArtinGroups.Coxeter.PositiveBraidRel

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  (hn:∀ a,Q.source a≠Q.target a)

lemma positiveWordAction_append (w z:List V) (x:FiniteHomotopyClass Q (K:=K)) :
    positiveWordAction Q (w++z) x=positiveWordAction Q w (positiveWordAction Q z x) := by
  induction w with
  | nil => rfl
  | cons a w ih => exact congrArg (classPositiveTwist Q a) ih

lemma classPacketPerm_positiveWord {J:Type u} [Fintype J] (v:J→V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b)) :
    ∃ w:List V,(∀ a∈w,∃ j,v j=a) ∧ ∀ x:FiniteHomotopyClass Q (K:=K),
      positiveWordAction Q w x=classPacketPerm Q hn v hv x := by
  suffices hh:∀ (J:Type u) [Fintype J] (v:J→V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b)),
    ∃ w:List V,(∀ a∈w,∃ j,v j=a) ∧ ∀ x:FiniteHomotopyClass Q (K:=K),
      positiveWordAction Q w x=classPacketPerm Q hn v hv x from hh J v hv
  intro J inst
  apply Fintype.induction_empty_option (P:=fun J _=>∀ (v:J→V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b)),
    ∃ w:List V,(∀ a∈w,∃ j,v j=a) ∧ ∀ x:FiniteHomotopyClass Q (K:=K),
      positiveWordAction Q w x=classPacketPerm Q hn v hv x) _ _ _ J
  · intro J L instL e ih
    let := Fintype.ofEquiv L e.symm
    intro v hv
    obtain ⟨w,hw,h⟩:=ih (v∘e) (fun a b hab=>hv (fun he=>hab (e.injective he)))
    refine ⟨w,fun a ha=>?_,?_⟩
    · obtain ⟨j,hj⟩:=hw a ha
      exact ⟨e j,hj⟩
    · intro x
      rw [classPacketPerm_reindex Q hn v hv e]
      exact h x
  · intro v hv
    refine ⟨[],by simp,?_⟩
    intro x
    rw [classPacketPerm_empty]
    rfl
  · intro J inst ih v hv
    obtain ⟨w,hw,h⟩:=ih (v∘some) (fun a b hab=>hv (fun he=>hab (Option.some.inj he)))
    refine ⟨v none::w,?_,?_⟩
    · intro a ha
      rcases List.mem_cons.mp ha with he|ha
      · exact ⟨none,he.symm⟩
      · obtain ⟨j,hj⟩:=hw a ha
        exact ⟨some j,hj⟩
    · intro x
      rw [classPacketPerm_cons]
      change classPositiveTwist Q (v none) (positiveWordAction Q w x)=_
      rw [h]
      rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
