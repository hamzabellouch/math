import Mathlib
import OAI.Topology.ArtinGroups.Complexes.Sum
import OAI.Topology.ArtinGroups.Complexes.LowerTruncation
import OAI.Topology.ArtinGroups.Complexes.SumTruncationEquiv

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type u} [Fintype I] [DecidableEq I]

omit [Fintype V] [DecidableEq A] in
lemma classLowerTruncation_sum (d:ℤ) (x:I→FiniteHomotopyClass Q (K:=K)) :
    classLowerTruncation Q d (classSum Q x)=classSum Q (fun i=>classLowerTruncation Q d (x i)) := by
  classical
  let E (i:I):=(minimalClassModel Q (x i)).complex
  have hE (i:I):(E i).IsMinimal Q:=minimalClassModel_minimal Q (x i)
  have hx:x=fun i=>classOfComplex Q (E i):=funext fun i=>(minimalClassModel_class Q (x i)).symm
  rw [hx,classSum_complex,classLowerTruncation_minimal Q _ (finiteSum_minimal Q E hE)]
  simp_rw [classLowerTruncation_minimal Q _ (hE _)]
  rw [classSum_complex,← sumTruncation_eq]
  exact classOfComplex_reindex Q _ _

omit [Fintype V] [DecidableEq A] in
lemma classLayer_sum (d:ℤ) (x:I→FiniteHomotopyClass Q (K:=K)) :
    classLayer Q d (classSum Q x)=classSum Q (fun i=>classLayer Q d (x i)) := by
  classical
  let E (i:I):=(minimalClassModel Q (x i)).complex
  have hE (i:I):(E i).IsMinimal Q:=minimalClassModel_minimal Q (x i)
  have hx:x=fun i=>classOfComplex Q (E i):=funext fun i=>(minimalClassModel_class Q (x i)).symm
  rw [hx,classSum_complex,classLayer_minimal Q _ (finiteSum_minimal Q E hE)]
  simp_rw [classLayer_minimal Q _ (hE _)]
  rw [classSum_complex,← sumLayer_eq]
  exact classOfComplex_reindex Q _ _

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
