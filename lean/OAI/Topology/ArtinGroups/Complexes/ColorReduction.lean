import Mathlib
import OAI.Topology.ArtinGroups.Complexes.TermwiseSplitInjection

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

lemma matrix_right_inverse_card_le {R:Matrix I J K} {S:Matrix J I K} (h:R*S=1) :
    Nat.card I≤Nat.card J := by
  have hi:Function.Injective R.toLinearMapRight' := by
    intro x y he
    have hh:=congrArg S.toLinearMapRight' he
    simpa only [← Matrix.toLinearMapRight'_mul_apply,h,Matrix.toLinearMapRight'_one,
      LinearMap.id_apply] using hh
  have hh:=LinearMap.finrank_le_finrank_of_injective hi
  simpa only [Module.finrank_fintype_fun_eq_card,Nat.card_eq_fintype_card] using hh

omit [Fintype V] [DecidableEq A] in
lemma TermwiseSplitInjection.multiplicity_le {E:BasedComplex Q (K:=K) I}
    {F:BasedComplex Q (K:=K) J} (f:TermwiseSplitInjection Q E F) (p:GeneratorPlacement V) :
    multiplicity Q E p ≤ multiplicity Q F p := by
  apply matrix_right_inverse_card_le (K:=K)
    (R:=reductionAt Q E.placement F.placement f.inclusion.matrix p)
    (S:=reductionAt Q F.placement E.placement f.retraction p)
  rw [← reductionAt_mul Q _ _ _ _ _ _ f.inclusion.entries f.inclusion.degree,
    f.split,reductionAt_identity]

def colorReduction (p:I→GeneratorPlacement V) (q:J→GeneratorPlacement V)
    (N:Matrix I J (Q.Zigzag K)) (α:V) :
    Matrix {i//(p i).color=α} {j//(q j).color=α} K := fun i j=>(N i.val j.val).vertex α

omit [Fintype V] [DecidableEq A] [Fintype I] in
lemma colorReduction_identity (p:I→GeneratorPlacement V) (α:V) :
    colorReduction Q p p (projectiveIdentity Q (K:=K) p) α=1 := by
  ext i j
  by_cases h:i=j
  · subst j
    simp [colorReduction,projectiveIdentity,i.property]
  · have h':(i:I)≠(j:I):=fun he=>h (Subtype.ext he)
    simp [colorReduction,projectiveIdentity,h,h']

omit [Fintype V] [DecidableEq A] [Fintype I] [DecidableEq I] [DecidableEq J] in
lemma colorReduction_mul {T:Type u} [Fintype T] (p:I→GeneratorPlacement V)
    (q:J→GeneratorPlacement V) (r:T→GeneratorPlacement V)
    (M:Matrix I J (Q.Zigzag K)) (N:Matrix J T (Q.Zigzag K)) (α:V)
    (hc:ProjectiveEntries Q p q M) :
    colorReduction Q p r (M*N) α=colorReduction Q p q M α*colorReduction Q q r N α := by
  apply Matrix.ext
  intro i z
  change (vertexHom Q (K:=K) α) ((M*N) i.val z.val)=_
  simp only [Matrix.mul_apply,map_sum,map_mul]
  apply Finset.sum_congr_set {j|(q j).color=α}
  · intro j hj
    rfl
  · intro j hj
    change (M i.val j).vertex α*(N j z.val).vertex α=0
    rw [entry_vertex_right_support Q hc i.val j α (Ne.symm hj),MulZeroClass.zero_mul]

omit [Fintype V] [DecidableEq A] in
lemma TermwiseSplitInjection.generatorVector_le {E:BasedComplex Q (K:=K) I}
    {F:BasedComplex Q (K:=K) J} (f:TermwiseSplitInjection Q E F) (α:V) :
    generatorVector Q E α≤generatorVector Q F α := by
  have h:colorReduction Q E.placement F.placement f.inclusion.matrix α*
      colorReduction Q F.placement E.placement f.retraction α=1 := by
    rw [← colorReduction_mul Q _ _ _ _ _ _ f.inclusion.entries,f.split,colorReduction_identity]
  have hn:=matrix_right_inverse_card_le h
  unfold generatorVector
  exact_mod_cast hn

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
