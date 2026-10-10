import Mathlib
import OAI.Topology.ArtinGroups.Complexes.Identity
import OAI.Topology.ArtinGroups.Complexes.PositiveTwistHomotopy
import OAI.Topology.ArtinGroups.Complexes.NormalizedInverseTwistHomotopy
import OAI.Topology.ArtinGroups.Complexes.NormalizedReverseTwistHomotopy
import OAI.Topology.ArtinGroups.Complexes.CommuteTwistSwap
import OAI.Topology.ArtinGroups.Coxeter.BraidCorePlacement

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

universe u

variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

def finiteHomotopySetoid : Setoid (FiniteModel.{u} Q (K := K)) where
  r E F := Nonempty (HomotopyEquivalence Q E.complex F.complex)
  iseqv := {
    refl E := ⟨HomotopyEquivalence.refl Q E.complex⟩
    symm := fun ⟨e⟩ => ⟨e.symm Q⟩
    trans := fun ⟨e⟩ ⟨f⟩ => ⟨e.trans Q f⟩ }

abbrev FiniteHomotopyClass := Quotient (finiteHomotopySetoid Q (K := K))

noncomputable def classPositiveTwist (α : V) :
    FiniteHomotopyClass Q (K := K) → FiniteHomotopyClass Q (K := K) :=
  Quotient.map (fun E => FiniteModel.ofComplex Q (E.complex.positiveTwist Q α))
    (by
      intro E F ⟨e⟩
      change Nonempty (HomotopyEquivalence Q (E.complex.positiveTwist Q α)
        (F.complex.positiveTwist Q α))
      refine ⟨?_⟩
      convert e.positiveTwist Q α using 1)

noncomputable def classNegativeTwist (α : V) :
    FiniteHomotopyClass Q (K := K) → FiniteHomotopyClass Q (K := K) :=
  Quotient.map (fun E => FiniteModel.ofComplex Q (E.complex.negativeTwist Q α))
    (by
      intro E F ⟨e⟩
      change Nonempty (HomotopyEquivalence Q (E.complex.negativeTwist Q α)
        (F.complex.negativeTwist Q α))
      refine ⟨?_⟩
      convert e.negativeTwist Q α using 1)

noncomputable def classTwistPerm (hn : ∀ a, Q.source a ≠ Q.target a) (α : V) :
    Equiv.Perm (FiniteHomotopyClass Q (K := K)) where
  toFun := classPositiveTwist Q α
  invFun := classNegativeTwist Q α
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with | _ E =>
      apply Quotient.sound
      exact ⟨negative_positive_homotopyEquivalence Q hn E.complex α⟩
  right_inv := by
    intro x
    induction x using Quotient.inductionOn with | _ E =>
      apply Quotient.sound
      exact ⟨positive_negative_homotopyEquivalence Q hn E.complex α⟩

lemma classTwistPerm_orthogonal (hn : ∀ a, Q.source a ≠ Q.target a)
    {α β : V} (h : OrthogonalVertices Q α β) :
    classTwistPerm Q (K := K) hn α * classTwistPerm Q hn β =
      classTwistPerm Q hn β * classTwistPerm Q hn α := by
  apply Equiv.ext
  intro x
  induction x using Quotient.inductionOn with | _ E =>
    apply Quotient.sound
    exact ⟨orthogonal_positiveTwists Q E.complex h⟩

lemma classTwistPerm_adjacent (hn : ∀ a, Q.source a ≠ Q.target a)
    {α β : V} (e : SimpleEdge Q α β) :
    classTwistPerm Q (K := K) hn α * classTwistPerm Q hn β * classTwistPerm Q hn α =
      classTwistPerm Q hn β * classTwistPerm Q hn α * classTwistPerm Q hn β := by
  apply Equiv.ext
  intro x
  induction x using Quotient.inductionOn with | _ E =>
    apply Quotient.sound
    exact ⟨adjacent_positiveTwists Q hn E.complex e⟩

namespace FiniteModel

noncomputable def minimalRepresentative (E : FiniteModel.{u} Q (K := K)) :
    FiniteModel.{u} Q (K := K) := (E.exists_minimal Q).choose

omit [Fintype V] [DecidableEq A] in
lemma minimalRepresentative_minimal (E : FiniteModel.{u} Q (K := K)) :
    (E.minimalRepresentative Q).complex.IsMinimal Q := (E.exists_minimal Q).choose_spec.1

noncomputable def minimalRepresentativeEquivalence (E : FiniteModel.{u} Q (K := K)) :
    HomotopyEquivalence Q E.complex (E.minimalRepresentative Q).complex :=
  (E.exists_minimal Q).choose_spec.2.some

end FiniteModel

noncomputable def classMultiplicity (a : GeneratorPlacement V) :
    FiniteHomotopyClass Q (K := K) → ℕ :=
  Quotient.lift (fun E => (E.minimalRepresentative Q).complex.multiplicity Q a)
    (by
      intro E F h
      obtain ⟨e⟩ := h
      exact multiplicity_eq_of_minimal_homotopyEquivalence Q _ _
        (E.minimalRepresentative_minimal Q) (F.minimalRepresentative_minimal Q)
        (((E.minimalRepresentativeEquivalence Q).symm Q).trans Q
          (e.trans Q (F.minimalRepresentativeEquivalence Q))) a)

omit [Fintype V] [DecidableEq A] in
lemma classMultiplicity_of_minimal (E : FiniteModel.{u} Q (K := K))
    (hE : E.complex.IsMinimal Q) (a : GeneratorPlacement V) :
    classMultiplicity Q a (Quotient.mk (finiteHomotopySetoid Q) E) =
      E.complex.multiplicity Q a := by
  exact (multiplicity_eq_of_minimal_homotopyEquivalence Q _ _ hE
    (E.minimalRepresentative_minimal Q) (E.minimalRepresentativeEquivalence Q) a).symm

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
