import Mathlib
import OAI.Topology.ArtinGroups.Complexes.HomDimension2
import OAI.Topology.ArtinGroups.Complexes.HomDimensionZeroHom

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def initialClass (α : V) : FiniteHomotopyClass Q (K := K) :=
  Quotient.mk (finiteHomotopySetoid Q) (FiniteModel.ofComplex Q (initialProjective Q α))

noncomputable def unfoldedFrame (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M) (α : V) :
    FiniteHomotopyClass Q (K := K) :=
  unfoldedArtinAction Q hn M hM x (initialClass Q α)

lemma unfoldedFrame_homDimension (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M)
    (α β : V) (n v : ℤ) :
    classHomDimension Q n v (unfoldedFrame Q (K := K) hn M hM x α)
      (unfoldedFrame Q hn M hM x β) =
    homDimension Q (initialProjective Q α : BasedComplex Q (K := K) PUnit.{u+1})
      (initialProjective Q β : BasedComplex Q (K := K) PUnit.{u+1}) n v :=
  unfoldedArtinAction_homDimension Q hn M hM x n v (initialClass Q α) (initialClass Q β)

lemma unfoldedFrame_self_bound (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M)
    (α : V) (n v : ℤ) :
    classHomDimension Q n v (unfoldedFrame Q (K := K) hn M hM x α)
      (unfoldedFrame Q hn M hM x α) ≤ 1 := by
  rw [unfoldedFrame_homDimension]
  exact initial_homDimension_le_one Q hn α n v

lemma unfoldedFrame_self_support (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M)
    (α : V) (n v : ℤ) (h : n ≠ 0 ∨ (v ≠ 0 ∧ v ≠ 2)) :
    classHomDimension Q n v (unfoldedFrame Q (K := K) hn M hM x α)
      (unfoldedFrame Q hn M hM x α) = 0 := by
  rw [unfoldedFrame_homDimension]
  rcases h with hn' | ⟨h₀, h₂⟩
  · exact initial_homDimension_nonzero_cochain Q α α n v hn'
  · exact initial_homDimension_other_internal Q hn α n v h₀ h₂

lemma unfoldedFrame_orthogonal (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M)
    {α β : V} (h : OrthogonalVertices Q α β) (n v : ℤ) :
    classHomDimension Q n v (unfoldedFrame Q (K := K) hn M hM x α)
      (unfoldedFrame Q hn M hM x β) = 0 := by
  rw [unfoldedFrame_homDimension]
  exact initial_homDimension_orthogonal Q h n v

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
