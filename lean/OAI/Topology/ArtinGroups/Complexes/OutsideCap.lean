import Mathlib
import OAI.Topology.ArtinGroups.Complexes.UpperBound
import OAI.Topology.ArtinGroups.Complexes.TestExact

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type u} [Fintype I] [DecidableEq I]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma scalarExact_of_absent_degree (E:BasedComplex Q (K:=K) I) (α:V) (l c:ℤ)
    (h:∀ i,(E.placement i).level≠l) : ScalarExactAt Q E α l c := by
  intro x hx _
  have hz:x=0 := by funext i; exact hx i (fun hh=>h i hh.1)
  refine ⟨0,?_,?_⟩
  · intro index _; rfl
  · rw [Matrix.zero_vecMul,hz]

omit [DecidableEq I] in
lemma testUpperBound_of_generator_cap (E:BasedComplex Q (K:=K) I) (d:ℤ)
    (h:∀ i,(E.placement i).level≤d) (U:Set V) : TestUpperBound Q E U (d+2) := by
  intro α _ l hl c
  apply scalarExact_of_absent_degree Q _ α l c
  intro j he
  have hp:Path.length j.2.val≤2 := by rcases j.2.val with v|a|v <;> norm_num [Path.length]
  have hi:=h j.1
  dsimp only [testComplex,testPlacement,GeneratorPlacement.level] at he hi
  omega

lemma classTestUpper_of_generator_cap (x:FiniteHomotopyClass Q (K:=K)) (d:ℤ)
    (h:ClassUpperBound Q d x) (U:Set V) : ClassTestUpper Q x U (d+2) := by
  rw [← minimalClassModel_class Q x]
  exact testUpperBound_of_generator_cap Q _ d h U

def ClassOutsideCap (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) (d:ℤ) : Prop :=
  ∀ i,((minimalClassModel Q x).complex.placement i).color∉U→
    ((minimalClassModel Q x).complex.placement i).level≤d

omit [Fintype V] [DecidableEq A] in
lemma classOutsideCap_of_upper (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) (d:ℤ)
    (h:ClassUpperBound Q d x) : ClassOutsideCap Q x U d := fun i _=>h i

lemma classPositiveTwist_outside_cap (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (d:ℤ) (α:V) (hα:α∈U) (h:ClassOutsideCap Q x U d) :
    ClassOutsideCap Q (classPositiveTwist Q α x) U d := by
  let E:=minimalClassModel Q x
  let F:=E.complex.positiveTwist Q α
  have hx:classOfComplex Q F=classPositiveTwist Q α x := by
    change classPositiveTwist Q α (classOfComplex Q E.complex)=_
    exact congrArg (classPositiveTwist Q α) (minimalClassModel_class Q x)
  rw [← hx]
  apply minimal_bound_transport Q F _ (minimalClassModel_minimal Q _)
    (minimalClassModelEquivalence Q F).symm (fun p=>p.color∉U→p.level≤d)
  intro i hi
  rcases i with j|j
  · exact (hi hα).elim
  · exact h j hi

lemma classUpperBound_of_test_and_outside (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (d:ℤ) (h:ClassTestUpper Q x U (d+2)) (ho:ClassOutsideCap Q x U d) :
    ClassUpperBound Q d x := by
  apply generatorBound_of_test_and_outside Q _ (minimalClassModel_minimal Q x) U d _ ho
  change ClassTestUpper Q (classOfComplex Q (minimalClassModel Q x).complex) U (d+2)
  have he:classOfComplex Q (minimalClassModel Q x).complex=x:=minimalClassModel_class Q x
  rw [he]
  exact h

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
