import Mathlib
import OAI.Topology.ArtinGroups.Complexes.NormalizedInverseTwistHomotopy
import OAI.Topology.ArtinGroups.Complexes.TokenShift

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [DecidableEq J] in
lemma test_homotopy_equation {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J}
    (f : Map Q E F) (g : Map Q F E) (α : V)
    {h : Matrix I I (Q.Zigzag K)} (hh : ProjectiveEntries Q E.placement E.placement h)
    (he : f.matrix * g.matrix = projectiveIdentity Q E.placement +
      (E.differential * h + h * E.differential)) :
    (f.test Q α).matrix * (g.test Q α).matrix =
      projectiveIdentity Q (E.testComplex Q α).placement +
      ((E.testComplex Q α).differential * testTransform Q E.placement E.placement α h +
        testTransform Q E.placement E.placement α h * (E.testComplex Q α).differential) := by
  change testTransform Q _ _ α f.matrix * testTransform Q _ _ α g.matrix =
    projectiveIdentity Q (testPlacement Q E.placement α) +
      (testTransform Q _ _ α E.differential * testTransform Q _ _ α h +
        testTransform Q _ _ α h * testTransform Q _ _ α E.differential)
  rw [testTransform_mul Q α _ f.entries, testTransform_mul Q α _ E.entries,
    testTransform_mul Q α _ hh, he, testTransform_add, testTransform_add,
    testTransform_identity]
  congr 2
  exact Subsingleton.elim _ _

noncomputable def HomotopyEquivalence.test {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (e : HomotopyEquivalence Q E F) (α : V) :
    HomotopyEquivalence Q (E.testComplex Q α) (F.testComplex Q α) where
  forward := e.forward.test Q α
  backward := e.backward.test Q α
  sourceHomotopy := testTransform Q E.placement E.placement α e.sourceHomotopy
  targetHomotopy := testTransform Q F.placement F.placement α e.targetHomotopy
  sourceEntries := scalarCornerMatrix_entries Q α _ _ (fun _ => rfl) (fun _ => rfl) _
  targetEntries := scalarCornerMatrix_entries Q α _ _ (fun _ => rfl) (fun _ => rfl) _
  sourceDegree := testMatrix_degree Q α e.sourceDegree
  targetDegree := testMatrix_degree Q α e.targetDegree
  sourceEquation := test_homotopy_equation Q e.forward e.backward α
    e.sourceEntries e.sourceEquation
  targetEquation := test_homotopy_equation Q e.backward e.forward α
    e.targetEntries e.targetEquation

noncomputable def negativeTwist_testShift (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    HomotopyEquivalence Q (((E.negativeTwist Q α).testComplex Q α).tokenShift Q)
      (E.testComplex Q α) :=
  ((positiveTwist_testShift Q hn (E.negativeTwist Q α) α).symm Q).trans Q
    ((positive_negative_homotopyEquivalence Q hn E α).test Q α)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
