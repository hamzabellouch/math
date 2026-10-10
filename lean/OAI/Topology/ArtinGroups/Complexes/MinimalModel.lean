import Mathlib
import OAI.Topology.ArtinGroups.Complexes.Initial
import OAI.Topology.ArtinGroups.Quivers.LinearMatrix

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def minimalClassModel (x : FiniteHomotopyClass Q (K := K)) :
    FiniteModel.{u} Q (K := K) := (Quotient.out x).minimalRepresentative Q

omit [Fintype V] [DecidableEq A] in
lemma minimalClassModel_minimal (x : FiniteHomotopyClass Q (K := K)) :
    (minimalClassModel Q x).complex.IsMinimal Q :=
  FiniteModel.minimalRepresentative_minimal Q _

omit [Fintype V] [DecidableEq A] in
lemma minimalClassModel_class (x : FiniteHomotopyClass Q (K := K)) :
    Quotient.mk (finiteHomotopySetoid Q) (minimalClassModel Q x) = x := by
  calc
    _ = Quotient.mk (finiteHomotopySetoid Q) (Quotient.out x) :=
      Quotient.sound ⟨((Quotient.out x).minimalRepresentativeEquivalence Q).symm Q⟩
    _ = x := Quotient.out_eq x

omit [DecidableEq A] in
lemma minimalClassModel_homDimension (x y : FiniteHomotopyClass Q (K := K)) (n v : ℤ) :
    homDimension Q (minimalClassModel Q x).complex (minimalClassModel Q y).complex n v =
      classHomDimension Q n v x y := by
  change classHomDimension Q n v (Quotient.mk _ (minimalClassModel Q x))
    (Quotient.mk _ (minimalClassModel Q y)) = _
  rw [minimalClassModel_class, minimalClassModel_class]

noncomputable def frameModel (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M) (α : V) :
    FiniteModel.{u} Q (K := K) := minimalClassModel Q (unfoldedFrame Q hn M hM x α)

lemma frameModel_minimal (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M) (α : V) :
    (frameModel Q (K := K) hn M hM x α).complex.IsMinimal Q := minimalClassModel_minimal Q _

lemma frameModel_linear_cycle_boundary (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M) (α : V)
    (n v : ℤ) {f : Matrix (frameModel Q (K := K) hn M hM x α).Index
      (frameModel Q (K := K) hn M hM x α).Index (Q.Zigzag K)}
    (hf : f ∈ homCycles Q (frameModel Q hn M hM x α).complex
      (frameModel Q hn M hM x α).complex n v) (hlin : LinearMatrix Q f) :
    f ∈ homBoundaries Q (frameModel Q hn M hM x α).complex
      (frameModel Q hn M hM x α).complex n v := by
  apply linear_selfCycle_boundary Q _ (frameModel_minimal Q hn M hM x α) _ _ n v hf hlin
  · intro n v
    rw [frameModel, minimalClassModel_homDimension]
    exact unfoldedFrame_self_bound Q hn M hM x α n v
  · intro n v h
    rw [frameModel, minimalClassModel_homDimension]
    exact unfoldedFrame_self_support Q hn M hM x α n v h

lemma frameModel_orthogonal_cycle_boundary (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M)
    {α β : V} (h : OrthogonalVertices Q α β)
    (n v : ℤ) {f : Matrix (frameModel Q (K := K) hn M hM x α).Index
      (frameModel Q (K := K) hn M hM x β).Index (Q.Zigzag K)}
    (hf : f ∈ homCycles Q (frameModel Q hn M hM x α).complex
      (frameModel Q hn M hM x β).complex n v) :
    f ∈ homBoundaries Q (frameModel Q hn M hM x α).complex
      (frameModel Q hn M hM x β).complex n v := by
  apply boundary_of_homDimension_zero Q _ _ n v _ hf
  exact (minimalClassModel_homDimension Q (unfoldedFrame Q (K := K) hn M hM x α)
    (unfoldedFrame Q hn M hM x β) n v).trans
    (unfoldedFrame_orthogonal Q (K := K) hn M hM x h n v)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
