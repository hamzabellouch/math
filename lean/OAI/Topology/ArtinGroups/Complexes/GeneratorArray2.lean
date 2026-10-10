import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PositiveTwistFiberEquiv
import OAI.Topology.ArtinGroups.Complexes.FiniteHomotopySetoid
import OAI.Topology.ArtinGroups.Complexes.GeneratorArray

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

universe u

variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def classGeneratorArray :
    FiniteHomotopyClass Q (K := K) → (GeneratorPlacement V →₀ ℕ) :=
  Quotient.lift (fun E => (E.minimalRepresentative Q).complex.generatorArray Q)
    (by
      intro E F h
      obtain ⟨e⟩ := h
      exact generatorArray_eq_of_minimal_homotopyEquivalence Q _ _
        (E.minimalRepresentative_minimal Q) (F.minimalRepresentative_minimal Q)
        (((E.minimalRepresentativeEquivalence Q).symm Q).trans Q
          (e.trans Q (F.minimalRepresentativeEquivalence Q))))

noncomputable def classLevelArray (x : FiniteHomotopyClass Q (K := K)) : V × ℤ →₀ ℕ :=
  (classGeneratorArray Q x).mapDomain (fun a => (a.color, a.level))

omit [Fintype V] [DecidableEq A] in
lemma classGeneratorArray_of_minimal (E : FiniteModel.{u} Q (K := K))
    (hE : E.complex.IsMinimal Q) :
    classGeneratorArray Q (Quotient.mk (finiteHomotopySetoid Q) E) =
      E.complex.generatorArray Q := by
  exact (generatorArray_eq_of_minimal_homotopyEquivalence Q _ _ hE
    (E.minimalRepresentative_minimal Q) (E.minimalRepresentativeEquivalence Q)).symm

omit [Fintype V] [DecidableEq A] in
lemma classLevelArray_of_minimal (E : FiniteModel.{u} Q (K := K))
    (hE : E.complex.IsMinimal Q) :
    classLevelArray Q (Quotient.mk (finiteHomotopySetoid Q) E) =
      E.complex.levelArray Q := by
  unfold classLevelArray levelArray
  rw [classGeneratorArray_of_minimal Q E hE]

omit [Fintype V] [DecidableEq A] in
lemma classGeneratorArray_apply (x : FiniteHomotopyClass Q (K := K))
    (a : GeneratorPlacement V) :
    classGeneratorArray Q x a = classMultiplicity Q a x := by
  induction x using Quotient.inductionOn with | _ E =>
    exact generatorArray_apply Q (E.minimalRepresentative Q).complex a

omit [Fintype V] [DecidableEq A] in
lemma class_eq_minimalRepresentative (E : FiniteModel.{u} Q (K := K)) :
    Quotient.mk (finiteHomotopySetoid Q) E =
      Quotient.mk (finiteHomotopySetoid Q) (E.minimalRepresentative Q) := by
  exact Quotient.sound ⟨E.minimalRepresentativeEquivalence Q⟩

lemma classPositiveTwist_exterior (x : FiniteHomotopyClass Q (K := K))
    (α : V) (a : GeneratorPlacement V) (hα : α ≠ a.color) :
    classGeneratorArray Q (classPositiveTwist Q α x) a = classGeneratorArray Q x a := by
  induction x using Quotient.inductionOn with | _ E =>
    rw [class_eq_minimalRepresentative Q E]
    let M := E.minimalRepresentative Q
    let T := FiniteModel.ofComplex Q (M.complex.positiveTwist Q α)
    change classGeneratorArray Q (Quotient.mk (finiteHomotopySetoid Q) T) a =
      classGeneratorArray Q (Quotient.mk (finiteHomotopySetoid Q) M) a
    rw [classGeneratorArray_of_minimal Q M (E.minimalRepresentative_minimal Q)]
    change (T.minimalRepresentative Q).complex.generatorArray Q a = M.complex.generatorArray Q a
    simp only [generatorArray_apply]
    refine positiveTwist_exterior_multiplicity Q M.complex _
      (E.minimalRepresentative_minimal Q) (T.minimalRepresentative_minimal Q) α
      ?_ a hα
    convert T.minimalRepresentativeEquivalence Q using 1 <;> rfl

lemma classNegativeTwist_exterior (x : FiniteHomotopyClass Q (K := K))
    (α : V) (a : GeneratorPlacement V) (hα : α ≠ a.color) :
    classGeneratorArray Q (classNegativeTwist Q α x) a = classGeneratorArray Q x a := by
  induction x using Quotient.inductionOn with | _ E =>
    rw [class_eq_minimalRepresentative Q E]
    let M := E.minimalRepresentative Q
    let T := FiniteModel.ofComplex Q (M.complex.negativeTwist Q α)
    change classGeneratorArray Q (Quotient.mk (finiteHomotopySetoid Q) T) a =
      classGeneratorArray Q (Quotient.mk (finiteHomotopySetoid Q) M) a
    rw [classGeneratorArray_of_minimal Q M (E.minimalRepresentative_minimal Q)]
    change (T.minimalRepresentative Q).complex.generatorArray Q a = M.complex.generatorArray Q a
    simp only [generatorArray_apply]
    refine negativeTwist_exterior_multiplicity Q M.complex _
      (E.minimalRepresentative_minimal Q) (T.minimalRepresentative_minimal Q) α
      ?_ a hα
    convert T.minimalRepresentativeEquivalence Q using 1 <;> rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
