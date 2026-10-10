import Mathlib
import OAI.Topology.ArtinGroups.Model
import OAI.Topology.ArtinGroups.Complexes.FiniteHomotopySetoid

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

universe u

variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

structure UnfoldedPresentation (M : CoxeterMatrix V) : Prop where
  relation (α β : V) : α = β ∨ M α β = 0 ∨
    (M α β = 2 ∧ OrthogonalVertices Q α β) ∨
    (M α β = 3 ∧ Nonempty (SimpleEdge Q α β))

lemma unfoldedTwist_relators (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) :
    ∀ r ∈ braidRelators M,
      FreeGroup.lift (classTwistPerm Q (K := K) hn) r = 1 := by
  rintro r ⟨⟨α, β⟩, rfl⟩
  rw [map_mul, map_inv]
  apply mul_inv_eq_one.mpr
  rcases hM.relation α β with hab | hzero | ⟨htwo, ho⟩ | ⟨hthree, ⟨he⟩⟩
  · subst β
    rfl
  · simp only [hzero, alternating]
  · simp only [htwo, alternating, map_mul, FreeGroup.lift_apply_of, _root_.mul_one]
    exact classTwistPerm_orthogonal Q hn ho
  · simp only [hthree, alternating, map_mul, FreeGroup.lift_apply_of, _root_.mul_one]
    simpa only [_root_.mul_assoc] using classTwistPerm_adjacent Q (K := K) hn he

noncomputable def unfoldedArtinAction (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) :
    Artin M →* Equiv.Perm (FiniteHomotopyClass Q (K := K)) :=
  PresentedGroup.toGroup (unfoldedTwist_relators Q hn M hM)

lemma unfoldedArtinAction_generator (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (α : V) :
    unfoldedArtinAction Q (K := K) hn M hM (generator M α) =
      classTwistPerm Q hn α := by
  exact PresentedGroup.toGroup.of _

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
