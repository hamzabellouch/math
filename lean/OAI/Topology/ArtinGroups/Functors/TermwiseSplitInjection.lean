import Mathlib
import OAI.Topology.ArtinGroups.Complexes.TermwiseSplitInjection
import OAI.Topology.ArtinGroups.Complexes.MinimalModelEquivalence
import OAI.Topology.ArtinGroups.Functors.ProbeEmbeddingMap

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
local notation "R" => probeQuiver Q

omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] [DecidableEq I] in
lemma coefficientTopDual_complex (E:BasedComplex Q (K:=K) I) (α:V) (c:ℤ) :
    coefficientTopDual R (complex Q E) (.inl α) c=coefficientTopDual Q E α c := by
  ext x
  constructor
  · rintro ⟨hs,hz⟩
    refine ⟨?_,?_⟩
    · intro i hi
      apply hs i
      simpa [complex,placement] using hi
    · intro i a
      exact hz i (.inl a)
  · rintro ⟨hs,hz⟩
    refine ⟨?_,?_⟩
    · intro i hi
      apply hs i
      simpa [complex,placement] using hi
    · intro i a
      cases a with
      | inl a=>exact hz i a
      | inr a=>simp only [complex,matrix,Matrix.map_apply,zigzag_arrow_leaf,MulZeroClass.zero_mul,Finset.sum_const_zero]

omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] [DecidableEq I] in
lemma coefficientSocle_complex (E:BasedComplex Q (K:=K) I) (α:V) (c:ℤ) :
    coefficientSocle R (complex Q E) (.inl α) c=coefficientSocle Q E α c := by
  ext x
  constructor
  · rintro ⟨hs,hz⟩
    refine ⟨?_,?_⟩
    · intro i hi
      apply hs i
      simpa [complex,placement] using hi
    · intro i a ha
      exact hz i (.inl a) (congrArg Sum.inl ha)
  · rintro ⟨hs,hz⟩
    refine ⟨?_,?_⟩
    · intro i hi
      apply hs i
      simpa [complex,placement] using hi
    · intro i a ha
      cases a with
      | inl a=>exact hz i a (Sum.inl.inj ha)
      | inr a=>simp only [complex,matrix,Matrix.map_apply,zigzag_arrow_leaf,MulZeroClass.mul_zero,Finset.sum_const_zero]

omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] [DecidableEq I] in
lemma pureLayer_complex (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (q:ℤ) :
    (complex Q E).pureLayer R (complex_minimal Q hE) q=complex Q (E.pureLayer Q hE q) := by
  apply ext_placement_differential R <;> rfl

omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] in
lemma classMap_layer (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ) :
    classLayer R q (classMap Q x)=classMap Q (classLayer Q q x) := by
  let E:=minimalClassModel Q x
  have hE:E.complex.IsMinimal Q:=minimalClassModel_minimal Q x
  rw [← minimalClassModel_class Q x]
  change classLayer R q (classMap Q (classOfComplex Q E.complex))=
    classMap Q (classLayer Q q (classOfComplex Q E.complex))
  erw [classMap_complex,classLayer_minimal R _ (complex_minimal Q hE),pureLayer_complex Q _ hE,
    classLayer_minimal Q _ hE,classMap_complex]
  rfl

lemma classLayerTopDimension_core (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ) (α:V) (c:ℤ) :
    classLayerTopDimension R q (.inl α) c (classMap Q x)=classLayerTopDimension Q q α c x := by
  let E:=minimalClassModel Q x
  have hE:E.complex.IsMinimal Q:=minimalClassModel_minimal Q x
  rw [← minimalClassModel_class Q x]
  change classLayerTopDimension R q (.inl α) c (classMap Q (classOfComplex Q E.complex))=
    classLayerTopDimension Q q α c (classOfComplex Q E.complex)
  erw [classMap_complex,
    classLayerTopDimension_minimal R _ (complex_minimal Q hE),
    classLayerTopDimension_minimal Q _ hE,pureLayer_complex Q E.complex hE q,coefficientTopDual_complex]
  rfl

lemma classLayerSocleDimension_core (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ) (α:V) (c:ℤ) :
    classLayerSocleDimension R q (.inl α) c (classMap Q x)=classLayerSocleDimension Q q α c x := by
  let E:=minimalClassModel Q x
  have hE:E.complex.IsMinimal Q:=minimalClassModel_minimal Q x
  rw [← minimalClassModel_class Q x]
  change classLayerSocleDimension R q (.inl α) c (classMap Q (classOfComplex Q E.complex))=
    classLayerSocleDimension Q q α c (classOfComplex Q E.complex)
  erw [classMap_complex,
    classLayerSocleDimension_minimal R _ (complex_minimal Q hE),
    classLayerSocleDimension_minimal Q _ hE,pureLayer_complex Q E.complex hE q,coefficientSocle_complex]
  rfl

noncomputable def termwiseSplitInjection {E:BasedComplex Q (K:=K) I}
    {F:BasedComplex Q (K:=K) J} (ι:TermwiseSplitInjection Q E F) :
    TermwiseSplitInjection R (complex Q E) (complex Q F) where
  inclusion:=chainMap Q ι.inclusion
  retraction:=matrix Q ι.retraction
  split:=by
    change matrix Q ι.inclusion.matrix*matrix Q ι.retraction=_
    rw [← matrix_mul,ι.split,matrix_identity]
    rfl

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
