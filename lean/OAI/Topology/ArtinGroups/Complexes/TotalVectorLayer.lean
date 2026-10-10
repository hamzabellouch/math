import Mathlib
import OAI.Topology.ArtinGroups.Complexes.GeneratorVectorPureLayer
import OAI.Topology.ArtinGroups.Complexes.NegativeTwistModern
import OAI.Topology.ArtinGroups.Complexes.TotalVector

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma classTotalVector_layer (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ) :
    classTotalVector Q (classLayer Q q x)=
      generatorVector Q ((minimalClassModel Q x).complex.pureLayer Q
        (minimalClassModel_minimal Q x) q) := by
  have h:=classSignedVector_pure Q (classLayer Q q x) q
    (classLayer_lowerBound Q x q) (classLayer_upperBound Q x q)
  have h':classSignedVector Q (classLayer Q q x)=
      cochainSign (K:=ℝ) q • generatorVector Q
        ((minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) q) :=
    signedGeneratorVector_pure Q _ q (fun i=>i.property)
  have hq:=congrArg (fun z:V→ℝ=>cochainSign (K:=ℝ) q • z) (h.symm.trans h')
  simpa only [smul_smul,cochainSign_mul_self,one_smul] using hq

omit [Fintype V] [DecidableEq A] in
lemma classTotalVector_layer_apply (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ) (α:V) :
    classTotalVector Q (classLayer Q q x) α=(classLevelArray Q x (α,q):ℝ) := by
  rw [classTotalVector_layer]
  exact generatorVector_minimalLayer Q x q α

omit [Fintype V] [DecidableEq A] in
lemma classLayer_eq_self_of_bounds (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hl:ClassLowerBound Q q x) (hh:ClassUpperBound Q q x) : classLayer Q q x=x := by
  have h:=classLayer_eq_self_of_pure Q (minimalClassModel Q x).complex
    (minimalClassModel_minimal Q x) q (fun i=>le_antisymm (hh i) (hl i))
  have hx:classOfComplex Q (minimalClassModel Q x).complex=x:=minimalClassModel_class Q x
  rw [hx] at h
  exact h

omit [Fintype V] [DecidableEq A] in
lemma classTotalVector_pure_apply (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hl:ClassLowerBound Q q x) (hh:ClassUpperBound Q q x) (α:V) :
    classTotalVector Q x α=(classLevelArray Q x (α,q):ℝ) := by
  exact (congrArg (fun y=>classTotalVector Q y α) (classLayer_eq_self_of_bounds Q x q hl hh)).symm.trans
    (classTotalVector_layer_apply Q x q α)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
