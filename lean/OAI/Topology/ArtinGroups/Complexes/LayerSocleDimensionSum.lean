import Mathlib
import OAI.Topology.ArtinGroups.Complexes.Sum
import OAI.Topology.ArtinGroups.Complexes.MinimalModelEquivalence
import OAI.Topology.ArtinGroups.Complexes.SumTestEquiv

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I : Type u} [Fintype I] [DecidableEq I]

lemma classLayerSocleDimension_sum (x : I → FiniteHomotopyClass Q (K := K))
    (d : ℤ) (α : V) (c : ℤ) :
    classLayerSocleDimension Q d α c (classSum Q x) =
      ∑ i, classLayerSocleDimension Q d α c (x i) := by
  classical
  let E (i:I) := (minimalClassModel Q (x i)).complex
  have hE (i:I) : (E i).IsMinimal Q := minimalClassModel_minimal Q (x i)
  have hx : x = fun i => classOfComplex Q (E i) := by
    funext i
    exact (minimalClassModel_class Q (x i)).symm
  conv_lhs => rw [hx,classSum_complex]
  rw [classLayerSocleDimension_minimal Q _ (finiteSum_minimal Q E hE)]
  rw [((sumLayerComparison Q E hE d).coefficientSocle Q
    (fun i => i.property) (fun i => i.2.property) α c).finrank_eq]
  rw [(coefficientSocleSumEquiv Q (fun i => (E i).pureLayer Q (hE i) d)
    (fun _ x => x.property) α c).finrank_eq,Module.finrank_pi_fintype]
  rfl

lemma classLayerTopDimension_sum (x : I → FiniteHomotopyClass Q (K := K))
    (d : ℤ) (α : V) (c : ℤ) :
    classLayerTopDimension Q d α c (classSum Q x) =
      ∑ i, classLayerTopDimension Q d α c (x i) := by
  classical
  let E (i:I) := (minimalClassModel Q (x i)).complex
  have hE (i:I) : (E i).IsMinimal Q := minimalClassModel_minimal Q (x i)
  have hx : x = fun i => classOfComplex Q (E i) := by
    funext i
    exact (minimalClassModel_class Q (x i)).symm
  conv_lhs => rw [hx,classSum_complex]
  rw [classLayerTopDimension_minimal Q _ (finiteSum_minimal Q E hE)]
  rw [((sumLayerComparison Q E hE d).coefficientTopDual Q
    (fun i => i.property) (fun i => i.2.property) α c).finrank_eq]
  rw [(coefficientTopSumEquiv Q (fun i => (E i).pureLayer Q (hE i) d)
    (fun _ x => x.property) α c).finrank_eq,Module.finrank_pi_fintype]
  rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
