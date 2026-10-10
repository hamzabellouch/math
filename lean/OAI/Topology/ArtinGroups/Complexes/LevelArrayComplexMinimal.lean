import Mathlib
import OAI.Topology.ArtinGroups.Complexes.GeneratorArray2
import OAI.Topology.ArtinGroups.Complexes.MinimalModel
import OAI.Topology.ArtinGroups.Complexes.Sum
import OAI.Topology.ArtinGroups.Complexes.SumTestEquiv

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  {I : Type u} [Fintype I] [DecidableEq I]

lemma classLevelArray_complex_minimal (E : BasedComplex Q (K := K) I) (hE : E.IsMinimal Q) :
    classLevelArray Q (classOfComplex Q E) = E.levelArray Q :=
  classLevelArray_of_minimal Q (FiniteModel.ofComplex Q E) hE

lemma finiteSum_levelArray {T : I → Type u} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
    (E : (i:I) → BasedComplex Q (K := K) (T i)) :
    (finiteSum Q E).levelArray Q = ∑ i, (E i).levelArray Q := by
  classical
  simp only [levelArray_eq_sum,Fintype.sum_sigma]
  rfl

lemma classLevelArray_sum (x : I → FiniteHomotopyClass Q (K := K)) :
    classLevelArray Q (classSum Q x) = ∑ i, classLevelArray Q (x i) := by
  classical
  let E (i:I) := (minimalClassModel Q (x i)).complex
  have hE (i:I) : (E i).IsMinimal Q := minimalClassModel_minimal Q (x i)
  have hx : x = fun i => classOfComplex Q (E i) := by
    funext i; exact (minimalClassModel_class Q (x i)).symm
  rw [hx,classSum_complex,classLevelArray_complex_minimal Q _ (finiteSum_minimal Q E hE)]
  simp_rw [classLevelArray_complex_minimal Q _ (hE _)]
  exact finiteSum_levelArray Q E

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
