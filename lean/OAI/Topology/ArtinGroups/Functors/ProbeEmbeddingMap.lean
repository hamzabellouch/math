import Mathlib
import OAI.Topology.ArtinGroups.Complexes.GeneratorArray2
import OAI.Topology.ArtinGroups.Complexes.MinimalModel
import OAI.Topology.ArtinGroups.Complexes.BasedComplexComplex
import OAI.Topology.ArtinGroups.Functors.TestIndex2

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
local notation "R" => probeQuiver Q

noncomputable def classMap : FiniteHomotopyClass Q (K:=K) → FiniteHomotopyClass R (K:=K) :=
  Quotient.map (fun E=>FiniteModel.ofComplex R (complex Q E.complex)) (by
    intro E F ⟨h⟩
    exact ⟨homotopyEquivalence Q h⟩)

omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] in
@[simp] lemma classMap_complex {I:Type u} [Fintype I] [DecidableEq I]
    (E:BasedComplex Q (K:=K) I) :
    classMap Q (classOfComplex Q E)=classOfComplex R (complex Q E) := rfl

lemma classMap_positiveTwist (α:V) (x:FiniteHomotopyClass Q (K:=K)) :
    classMap Q (classPositiveTwist Q α x)=classPositiveTwist R (.inl α) (classMap Q x) := by
  induction x using Quotient.inductionOn with | _ E =>
    change classOfComplex R (complex Q (E.complex.positiveTwist Q α))=
      classOfComplex R ((complex Q E.complex).positiveTwist R (.inl α))
    rw [← positiveTwist_transport]
    exact (classOfComplex_reindex R _ _).symm

lemma classMap_negativeTwist (hn:∀a,Q.source a≠Q.target a)
    (α:V) (x:FiniteHomotopyClass Q (K:=K)) :
    classMap Q (classNegativeTwist Q α x)=classNegativeTwist R (.inl α) (classMap Q x) := by
  apply (classTwistPerm R (probeQuiver_no_loops Q hn) (.inl α)).injective
  change classPositiveTwist R (.inl α) (classMap Q (classNegativeTwist Q α x))=_
  rw [← classMap_positiveTwist]
  exact congrArg (classMap Q) ((classTwistPerm Q hn α).apply_symm_apply x) |>.trans
    ((classTwistPerm R (probeQuiver_no_loops Q hn) (.inl α)).apply_symm_apply (classMap Q x)).symm

omit [Fintype V] [DecidableEq V] [DecidableEq (ProbeVertex V)] in
lemma placement_injective : Function.Injective (placement (V:=V)) := by
  intro p q h
  cases p with | mk v n t => cases q with | mk w m u =>
    simpa only [placement,GeneratorPlacement.mk.injEq,Sum.inl.injEq] using h

omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] in
lemma generatorArray_core {I:Type u} [Fintype I] (E:BasedComplex Q (K:=K) I)
    (p:GeneratorPlacement V) :
    (complex Q E).generatorArray R (placement p)=E.generatorArray Q p := by
  classical
  simp only [generatorArray,Finsupp.finsetSum_apply,Finsupp.single_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (if placement (E.placement i)=placement p then 1 else 0)=_
  simp only [placement_injective.eq_iff]

omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] in
lemma levelArray_core {I:Type u} [Fintype I] (E:BasedComplex Q (K:=K) I) (v:V) (d:ℤ) :
    (complex Q E).levelArray R (.inl v,d)=E.levelArray Q (v,d) := by
  classical
  simp only [levelArray_eq_sum,Finsupp.finsetSum_apply,Finsupp.single_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (if ((.inl (E.placement i).color:ProbeVertex V),(E.placement i).level)=(.inl v,d) then 1 else 0)=_
  simp only [Prod.mk.injEq,Sum.inl.injEq]

omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] in
lemma levelArray_leaf {I:Type u} [Fintype I] (E:BasedComplex Q (K:=K) I) (v:V) (b:Bool) (d:ℤ) :
    (complex Q E).levelArray R (.inr (v,b),d)=0 := by
  classical
  simp only [levelArray_eq_sum,Finsupp.finsetSum_apply,Finsupp.single_apply]
  apply Finset.sum_eq_zero
  intro i _
  change (if ((.inl (E.placement i).color:ProbeVertex V),(E.placement i).level)=(.inr (v,b),d) then 1 else 0)=0
  simp

omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] in
lemma classGeneratorArray_core (x:FiniteHomotopyClass Q (K:=K)) (p:GeneratorPlacement V) :
    classGeneratorArray R (classMap Q x) (placement p)=classGeneratorArray Q x p := by
  let E:=minimalClassModel Q x
  have hE:E.complex.IsMinimal Q:=minimalClassModel_minimal Q x
  rw [← minimalClassModel_class Q x]
  change classGeneratorArray R (classOfComplex R (complex Q E.complex)) _=_
  erw [classGeneratorArray_of_minimal R (FiniteModel.ofComplex R _) (complex_minimal Q hE),
    classGeneratorArray_of_minimal Q E hE]
  exact generatorArray_core Q E.complex p

omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] in
lemma classLevelArray_core (x:FiniteHomotopyClass Q (K:=K)) (v:V) (d:ℤ) :
    classLevelArray R (classMap Q x) (.inl v,d)=classLevelArray Q x (v,d) := by
  let E:=minimalClassModel Q x
  have hE:E.complex.IsMinimal Q:=minimalClassModel_minimal Q x
  rw [← minimalClassModel_class Q x]
  change classLevelArray R (classOfComplex R (complex Q E.complex)) _=_
  erw [classLevelArray_of_minimal R (FiniteModel.ofComplex R _) (complex_minimal Q hE),
    classLevelArray_of_minimal Q E hE]
  exact levelArray_core Q E.complex v d

omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] in
lemma classLevelArray_leaf (x:FiniteHomotopyClass Q (K:=K)) (v:V) (b:Bool) (d:ℤ) :
    classLevelArray R (classMap Q x) (.inr (v,b),d)=0 := by
  let E:=minimalClassModel Q x
  have hE:E.complex.IsMinimal Q:=minimalClassModel_minimal Q x
  rw [← minimalClassModel_class Q x]
  change classLevelArray R (classOfComplex R (complex Q E.complex)) _=0
  erw [classLevelArray_of_minimal R (FiniteModel.ofComplex R _) (complex_minimal Q hE)]
  exact levelArray_leaf Q E.complex v b d

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
