import Mathlib
import OAI.Topology.ArtinGroups.Complexes.BasedComplexComplex
import OAI.Topology.ArtinGroups.Complexes.FiniteSum2

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I : Type u} [Fintype I] [DecidableEq I]

noncomputable def classSum (x : I → FiniteHomotopyClass Q (K := K)) :
    FiniteHomotopyClass Q (K := K) := by
  classical
  exact classOfComplex Q (finiteSum Q (fun i => (x i).out.complex))

omit [Fintype V] [DecidableEq A] in
lemma classSum_mk (E : I → FiniteModel.{u} Q (K := K)) :
    classSum Q (fun i => Quotient.mk (finiteHomotopySetoid Q) (E i)) =
      classOfComplex Q (finiteSum Q (fun i => (E i).complex)) := by
  classical
  apply classOfComplex_eq
  apply HomotopyEquivalence.finiteSum
  intro i
  exact Classical.choice (Quotient.exact (Quotient.out_eq
    (Quotient.mk (finiteHomotopySetoid Q) (E i))))

omit [Fintype V] [DecidableEq A] in
lemma classSum_complex {T : I → Type u} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
    (E : (i:I) → BasedComplex Q (K := K) (T i)) :
    classSum Q (fun i => classOfComplex Q (E i)) = classOfComplex Q (finiteSum Q E) :=
  classSum_mk Q (fun i => FiniteModel.ofComplex Q (E i))

lemma classPositiveTwist_sum (α : V) (x : I → FiniteHomotopyClass Q (K := K)) :
    classPositiveTwist Q α (classSum Q x) =
      classSum Q (fun i => classPositiveTwist Q α (x i)) := by
  classical
  have hx : x = fun i => Quotient.mk (finiteHomotopySetoid Q) (x i).out := by
    funext i; exact (Quotient.out_eq (x i)).symm
  conv_rhs => rw [hx]
  change _ = classSum Q (fun i => classOfComplex Q ((x i).out.complex.positiveTwist Q α))
  rw [classSum_complex]
  change classOfComplex Q ((finiteSum Q (fun i => (x i).out.complex)).positiveTwist Q α) = _
  exact (classOfComplex_reindex Q _ (sumTwistEquiv Q (fun i => (x i).out.complex) α)).trans
    (congrArg (classOfComplex Q) (sumTwist_eq Q (fun i => (x i).out.complex) α))

lemma classNegativeTwist_sum (hn : ∀ a, Q.source a ≠ Q.target a) (α : V)
    (x : I → FiniteHomotopyClass Q (K := K)) :
    classNegativeTwist Q α (classSum Q x) =
      classSum Q (fun i => classNegativeTwist Q α (x i)) := by
  apply (classTwistPerm Q hn α).injective
  change (classTwistPerm Q hn α) ((classTwistPerm Q hn α).symm (classSum Q x)) = _
  rw [(classTwistPerm Q hn α).apply_symm_apply]
  change _ = classPositiveTwist Q α (classSum Q (fun i => (classTwistPerm Q hn α).symm (x i)))
  rw [classPositiveTwist_sum]
  simp only [show classPositiveTwist Q α = classTwistPerm Q hn α from rfl,Equiv.apply_symm_apply]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
