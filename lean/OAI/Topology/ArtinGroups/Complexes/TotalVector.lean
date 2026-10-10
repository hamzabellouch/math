import Mathlib
import OAI.Topology.ArtinGroups.Complexes.CanonicalWordLow
import OAI.Topology.ArtinGroups.Complexes.CochainSignSubOne

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
open Matrix
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def classTotalVector (x : FiniteHomotopyClass Q (K:=K)) : V → ℝ :=
  generatorVector Q (minimalClassModel Q x).complex

omit [Fintype V] [DecidableEq A] in
lemma classSignedVector_minimal (x : FiniteHomotopyClass Q (K:=K)) :
    classSignedVector Q x=signedGeneratorVector Q (minimalClassModel Q x).complex := by
  exact (congrArg (classSignedVector Q) (minimalClassModel_class Q x)).symm

omit [Fintype V] [DecidableEq A] in
lemma signedGeneratorVector_pure {I : Type u} [Fintype I]
    (E : BasedComplex Q (K:=K) I) (q : ℤ) (hE : ∀ i,(E.placement i).level=q) :
    signedGeneratorVector Q E=cochainSign (K:=ℝ) q • generatorVector Q E := by
  funext v
  simp only [signedGeneratorVector,placementSignedWeight,hE,generatorVector_sum,
    Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

omit [Fintype V] [DecidableEq A] in
lemma classSignedVector_pure (x : FiniteHomotopyClass Q (K:=K)) (q : ℤ)
    (hlo : ClassLowerBound Q q x) (hhi : ClassUpperBound Q q x) :
    classSignedVector Q x=cochainSign (K:=ℝ) q • classTotalVector Q x := by
  rw [classSignedVector_minimal]
  exact signedGeneratorVector_pure Q _ q (fun i=>le_antisymm (hhi i) (hlo i))

omit [Fintype V] [DecidableEq A] in
lemma signedGeneratorVector_upper_partition {I : Type u} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K:=K) I) (hE : E.IsMinimal Q)
    (q : ℤ) (hhi : ∀ i,(E.placement i).level≤q) :
    signedGeneratorVector Q E=signedGeneratorVector Q (lowerTruncation Q E hE (q-1))+
      signedGeneratorVector Q (E.pureLayer Q hE q) := by
  funext v
  simp only [signedGeneratorVector, lowerTruncation, lowRestriction, pureLayer, restrict, Pi.add_apply]
  have hlo : (∑ i : ↑(lowerLevelSet Q E (q-1)),placementSignedWeight (E.placement i) v)=
      ∑ i ∈ Finset.univ.filter (fun i : I=>(E.placement i).level≤q-1),
        placementSignedWeight (E.placement i) v := by
    symm
    apply Finset.sum_subtype
    intro i
    simp [lowerLevelSet]
  have hh : (∑ i : ↑{i : I | (E.placement i).level=q},placementSignedWeight (E.placement i) v)=
      ∑ i ∈ Finset.univ.filter (fun i : I=>(E.placement i).level=q),
        placementSignedWeight (E.placement i) v := by
    symm
    apply Finset.sum_subtype
    intro i
    simp
  rw [hlo,hh]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi:=hhi i
  by_cases he:(E.placement i).level≤q-1
  · have hn:(E.placement i).level≠q := by omega
    simp [he,hn]
  · have hn:(E.placement i).level=q := by omega
    simp [hn]

omit [Fintype V] [DecidableEq A] in
lemma classSignedVector_upper_partition (x : FiniteHomotopyClass Q (K:=K)) (q : ℤ)
    (hhi : ClassUpperBound Q q x) :
    classSignedVector Q x=classSignedVector Q (classLowerTruncation Q (q-1) x)+
      classSignedVector Q (classLayer Q q x) := by
  rw [classSignedVector_minimal Q x]
  exact signedGeneratorVector_upper_partition Q _ (minimalClassModel_minimal Q x) q hhi

lemma rowReflect_sub (C : Matrix V V ℝ) (α : V) (x y : V → ℝ) :
    rowReflect C α (x-y)=rowReflect C α x-rowReflect C α y := by
  simp only [rowReflect,Matrix.mulVec_sub,Pi.sub_apply,sub_smul]
  module

lemma rowReflect_smul (C : Matrix V V ℝ) (α : V) (a : ℝ) (x : V → ℝ) :
    rowReflect C α (a • x)=a • rowReflect C α x := by
  simp only [rowReflect,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul,smul_sub,smul_smul]

lemma rowReflectWord_sub (C : Matrix V V ℝ) (w : List V) (x y : V → ℝ) :
    rowReflectWord C w (x-y)=rowReflectWord C w x-rowReflectWord C w y := by
  induction w with
  | nil => rfl
  | cons α w ih =>
    change rowReflect C α (rowReflectWord C w (x-y))=_
    rw [ih,rowReflect_sub]
    rfl

lemma rowReflectWord_smul (C : Matrix V V ℝ) (w : List V) (a : ℝ) (x : V → ℝ) :
    rowReflectWord C w (a • x)=a • rowReflectWord C w x := by
  induction w with
  | nil => rfl
  | cons α w ih =>
    change rowReflect C α (rowReflectWord C w (a • x))=_
    rw [ih,rowReflect_smul]
    rfl

lemma classSignedVector_inverseWord (w : List V) (x : FiniteHomotopyClass Q (K:=K)) :
    classSignedVector Q (inverseWordAction Q w x)=
      rowReflectWord (unfoldedCartan Q) w.reverse (classSignedVector Q x) := by
  induction w generalizing x with
  | nil => rfl
  | cons α w ih =>
    change classSignedVector Q (inverseWordAction Q w (classNegativeTwist Q α x))=_
    rw [ih,classSignedVector_negativeTwist,List.reverse_cons,rowReflectWord_append]
    rfl

theorem canonicalLow_reflected_high_signed (hn : ∀ a,Q.source a≠Q.target a)
    (w : List V) (q : ℤ) (x : FiniteHomotopyClass Q (K:=K))
    (hhi : ClassUpperBound Q q x) :
    classSignedVector Q (classLayer Q q (inverseWordAction Q w x))=
      rowReflectWord (unfoldedCartan Q) w.reverse
        (classSignedVector Q x-classSignedVector Q (canonicalWordLow Q w q x)) := by
  have h:=classSignedVector_upper_partition Q (inverseWordAction Q w x) q
    (inverseWord_upper_bound Q w x hhi)
  have hl : classLowerTruncation Q (q-1) (inverseWordAction Q w x)=
      inverseWordAction Q w (canonicalWordLow Q w q x) :=
    (inverse_positiveWord Q hn w _).symm
  rw [hl,classSignedVector_inverseWord,classSignedVector_inverseWord] at h
  rw [rowReflectWord_sub]
  exact (eq_sub_iff_add_eq.mpr (by rw [add_comm]; exact h.symm))

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
