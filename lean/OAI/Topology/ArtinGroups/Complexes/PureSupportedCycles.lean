import Mathlib
import OAI.Topology.ArtinGroups.Quivers.UnitTestVector
import OAI.Topology.ArtinGroups.Quivers.TokenTestVector
import OAI.Topology.ArtinGroups.Diagrams.TransposeConjugateEquiv

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K I J : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype I] in
lemma testMatrix_identity (p : I → GeneratorPlacement V) (α : V) :
    testMatrix Q p p α (projectiveIdentity Q p (K := K)) = 1 := by
  apply Matrix.ext
  intro u v
  change pathCoordinates Q (pathBasis Q u.2.val *
    (if u.1 = v.1 then vertexId Q (p u.1).color else 0)) v.2.val = _
  by_cases hi : u.1 = v.1
  · rcases u with ⟨i,u⟩
    rcases v with ⟨j,v⟩
    dsimp only at hi
    subst j
    simp only [ite_true,cornerPath_right,pathBasis_coordinates]
    by_cases hp : u=v
    · subst v; simp
    · have hv : u.val ≠ v.val := fun h => hp (Subtype.ext h)
      simp [hp,hv]
  · rw [ite_eq_right hi,MulZeroClass.mul_zero,coordinates_zero]
    exact (Matrix.one_apply_ne (fun h => hi (congrArg Sigma.fst h))).symm

namespace BasedComplex

omit [DecidableEq I] [DecidableEq J] in
lemma pureMap_test_support {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (f : Map Q E F) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (hF : ∀ j, (F.placement j).level=l)
    (α : V) (c n : ℤ) (i : TestIndex Q E.placement α) (j : TestIndex Q F.placement α)
    (h : testMatrix Q E.placement F.placement α f.matrix i j ≠ 0) :
    ((E.placement i.1).cochain=c ∧ Path.length i.2.val=n) ↔
      ((F.placement j.1).cochain=c ∧ Path.length j.2.val=n) := by
  have he : (F.placement j.1).cochain = (E.placement i.1).cochain := by
    by_contra hh
    apply h
    unfold testMatrix
    rw [(f.degree i.1 j.1).1 (by simpa only [add_zero] using hh),
      MulZeroClass.mul_zero,coordinates_zero]
  have hh := pure_homSpace_homogeneous Q E F hE hF (n := 0) (v := 0) (r := 0)
    (by omega) ⟨f.entries,f.degree⟩ i.1 j.1
  have hp := coordinates_mul_degree Q (pathBasis_homogeneous Q i.2.val) hh h
  have hlen : Path.length j.2.val = Path.length i.2.val := by simpa only [add_zero] using hp
  rw [he,hlen]

noncomputable def ChainIsomorphism.pureSupportedCycles
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (f : ChainIsomorphism Q E F) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (hF : ∀ j, (F.placement j).level=l)
    (α : V) (c n : ℤ) :
    ScalarCycles.supportedKernel (testMatrix Q E.placement E.placement α E.differential)
      (fun i => (E.placement i.1).cochain=c ∧ Path.length i.2.val=n) ≃ₗ[K]
    ScalarCycles.supportedKernel (testMatrix Q F.placement F.placement α F.differential)
      (fun i => (F.placement i.1).cochain=c ∧ Path.length i.2.val=n) := by
  apply ScalarCycles.conjugateEquiv _ _ _ _
    (testMatrix Q E.placement F.placement α f.forward.matrix)
    (testMatrix Q F.placement E.placement α f.backward.matrix)
  · exact pureMap_test_support Q f.forward hE hF α c n
  · exact pureMap_test_support Q f.backward hF hE α c n
  · rw [testMatrix_mul Q α _ f.forward.entries,f.sourceEquation,testMatrix_identity]
  · rw [testMatrix_mul Q α _ f.backward.entries,f.targetEquation,testMatrix_identity]
  · rw [testMatrix_mul Q α _ E.entries,testMatrix_mul Q α _ f.forward.entries,f.forward.commute]

noncomputable def ChainIsomorphism.pureDualSupportedCycles
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (f : ChainIsomorphism Q E F) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (hF : ∀ j, (F.placement j).level=l)
    (α : V) (c n : ℤ) :
    ScalarCycles.supportedKernel (testMatrix Q E.placement E.placement α E.differential).transpose
      (fun i => (E.placement i.1).cochain=c ∧ Path.length i.2.val=n) ≃ₗ[K]
    ScalarCycles.supportedKernel (testMatrix Q F.placement F.placement α F.differential).transpose
      (fun i => (F.placement i.1).cochain=c ∧ Path.length i.2.val=n) := by
  apply ScalarCycles.transposeConjugateEquiv _ _ _ _
    (testMatrix Q E.placement F.placement α f.forward.matrix)
    (testMatrix Q F.placement E.placement α f.backward.matrix)
  · exact pureMap_test_support Q f.forward hE hF α c n
  · exact pureMap_test_support Q f.backward hF hE α c n
  · rw [testMatrix_mul Q α _ f.forward.entries,f.sourceEquation,testMatrix_identity]
  · rw [testMatrix_mul Q α _ f.backward.entries,f.targetEquation,testMatrix_identity]
  · rw [testMatrix_mul Q α _ F.entries,testMatrix_mul Q α _ f.backward.entries,f.backward.commute]

noncomputable def ChainIsomorphism.coefficientSocle
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (f : ChainIsomorphism Q E F) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (hF : ∀ j, (F.placement j).level=l)
    (α : V) (c : ℤ) :
    coefficientSocle Q E α c ≃ₗ[K] coefficientSocle Q F α c :=
  ((coefficientSocleTestEquiv Q E hE α c).trans
    (f.pureSupportedCycles Q hE hF α c 0)).trans
    (coefficientSocleTestEquiv Q F hF α c).symm

noncomputable def ChainIsomorphism.coefficientTopDual
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (f : ChainIsomorphism Q E F) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (hF : ∀ j, (F.placement j).level=l)
    (α : V) (c : ℤ) :
    coefficientTopDual Q E α c ≃ₗ[K] coefficientTopDual Q F α c :=
  ((coefficientTopTestEquiv Q E hE α c).trans
    (f.pureDualSupportedCycles Q hE hF α c 2)).trans
    (coefficientTopTestEquiv Q F hF α c).symm

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
