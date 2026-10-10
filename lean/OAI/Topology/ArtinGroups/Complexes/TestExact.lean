import Mathlib
import OAI.Topology.ArtinGroups.Complexes.FiniteHomotopySetoid
import OAI.Topology.ArtinGroups.Complexes.TestUpperBound
import OAI.Topology.ArtinGroups.Complexes.ScalarSupportedCochainShift

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

def ClassTestExact (α:V) (l c:ℤ) : FiniteHomotopyClass Q (K:=K)→Prop :=
  Quotient.lift (fun E=>ScalarExactAt Q (E.complex.testComplex Q α) α l c) (by
    intro E F h
    obtain ⟨e⟩:=h
    apply propext
    constructor
    · exact fun h=>scalarExact_transport Q _ _ ((e.symm Q).test Q α) α (fun _=>rfl) h
    · exact fun h=>scalarExact_transport Q _ _ (e.test Q α) α (fun _=>rfl) h)

def ClassTestUpper (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) (t:ℤ) : Prop :=
  ∀ α∈U,∀ l:ℤ,t<l→∀ c:ℤ,ClassTestExact Q α l c x

lemma classTestUpper_model (E:FiniteModel Q (K:=K)) (U:Set V) (t:ℤ) :
    ClassTestUpper Q ⟦E⟧ U t ↔ TestUpperBound Q E.complex U t := Iff.rfl

lemma classTestExact_positive_self (hn:∀ a,Q.source a≠Q.target a)
    (x:FiniteHomotopyClass Q (K:=K)) (α:V) (l c:ℤ) :
    ClassTestExact Q α l c (classPositiveTwist Q α x) ↔
      ClassTestExact Q α (l-1) (c+1) x := by
  induction x using Quotient.inductionOn with | _ E =>
    exact positiveTwist_test_exact_iff Q hn E.complex α l c

lemma classTestExact_positive_other (x:FiniteHomotopyClass Q (K:=K)) (α β:V)
    (hne:β≠α) (l c:ℤ)
    (ha:ClassTestExact Q α l (c+1) x) (hb:ClassTestExact Q β l c x) :
    ClassTestExact Q β l c (classPositiveTwist Q α x) := by
  induction x using Quotient.inductionOn with | _ E =>
    exact positiveTwist_other_test_exact Q E.complex α β hne l c ha hb

lemma classTestExact_positive_adjacent (hn:∀ a,Q.source a≠Q.target a)
    (x:FiniteHomotopyClass Q (K:=K)) {α β:V} (e:SimpleEdge Q α β) (l c:ℤ) :
    ClassTestExact Q β l c (classPositiveTwist Q α (classPositiveTwist Q β x)) ↔
      ClassTestExact Q α l (c+1) x := by
  induction x using Quotient.inductionOn with | _ E =>
    exact positiveTwist_adjacent_test_exact_iff Q hn E.complex e l c

lemma classPositiveTwist_testUpper (hn:∀ a,Q.source a≠Q.target a)
    (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) (α:V) (hα:α∈U) {t:ℤ}
    (h:ClassTestUpper Q x U t) : ClassTestUpper Q (classPositiveTwist Q α x) U (t+1) := by
  induction x using Quotient.inductionOn with | _ E =>
    exact positiveTwist_testUpperBound Q hn E.complex U α hα h

lemma classPositiveTwist_testUpper_reflect (hn:∀ a,Q.source a≠Q.target a)
    (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) (α:V) (hα:α∈U) {t:ℤ}
    (h:ClassTestUpper Q (classPositiveTwist Q α x) U t) : ClassTestUpper Q x U t := by
  induction x using Quotient.inductionOn with | _ E =>
    exact positiveTwist_testUpperBound_reflect Q hn E.complex U α hα h

lemma classPositiveTwist_testUpper_iff (hn:∀ a,Q.source a≠Q.target a)
    (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) (α:V) (hα:α∈U) {t:ℤ}
    (h:ClassTestUpper Q x U t) :
    ClassTestUpper Q (classPositiveTwist Q α x) U t ↔
      ∀ c,ClassTestExact Q α t c x := by
  induction x using Quotient.inductionOn with | _ E =>
    exact positiveTwist_testUpperBound_iff Q hn E.complex U α hα h

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
