import Mathlib
import OAI.Topology.ArtinGroups.Quivers.SmulMul

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K:Type*} (Q:ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

def BlockClosed (E:BasedComplex Q (K:=K) I) (T:Set I) : Prop :=
  ∀ i j, E.differential i j ≠ 0 → (i∈T ↔ j∈T)

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma BlockClosed.restrict_condition {E:BasedComplex Q (K:=K) I} {T:Set I}
    (h:BlockClosed Q E T) : ∀ i∈T,∀ j∈T,∀ k∉T,E.differential i k*E.differential k j=0 := by
  intro i hi j _ k hk
  have hz:E.differential i k=0 := by
    by_contra hh
    exact hk ((h i k hh).mp hi)
  rw [hz,zero_mul]

noncomputable def blockRestriction (E:BasedComplex Q (K:=K) I) (T:Set I)
    (h:BlockClosed Q E T) : BasedComplex Q (K:=K) T :=
  E.restrict Q T h.restrict_condition

noncomputable def blockInclusion (E:BasedComplex Q (K:=K) I) (T:Set I) : Matrix T I (Q.Zigzag K) :=
  (projectiveIdentity Q E.placement).submatrix Subtype.val id
noncomputable def blockProjection (E:BasedComplex Q (K:=K) I) (T:Set I) : Matrix I T (Q.Zigzag K) :=
  (projectiveIdentity Q E.placement).submatrix id Subtype.val

omit [Fintype V] [DecidableEq A] in
lemma blockInclusion_entries (E:BasedComplex Q (K:=K) I) (T:Set I) :
    ProjectiveEntries Q (fun i:T=>E.placement i) E.placement (blockInclusion Q E T) :=
  ⟨fun i j=>(projectiveEntries_identity Q).1 (i:I) j,
   fun i j=>(projectiveEntries_identity Q).2 (i:I) j⟩
omit [Fintype V] [DecidableEq A] in
lemma blockProjection_entries (E:BasedComplex Q (K:=K) I) (T:Set I) :
    ProjectiveEntries Q E.placement (fun i:T=>E.placement i) (blockProjection Q E T) :=
  ⟨fun i j=>(projectiveEntries_identity Q).1 i (j:I),
   fun i j=>(projectiveEntries_identity Q).2 i (j:I)⟩

omit [Fintype V] [DecidableEq A] in
lemma blockInclusion_mul (E:BasedComplex Q (K:=K) I) (T:Set I)
    {J:Type*} (p:J → GeneratorPlacement V) (M:Matrix I J (Q.Zigzag K))
    (hM:ProjectiveEntries Q E.placement p M) :
    blockInclusion Q E T*M=M.submatrix Subtype.val id := by
  apply Matrix.ext
  intro i j
  change (∑ k,(if (i:I)=k then vertexId Q (K:=K) (E.placement i).color else 0)*M k j)=M i j
  simp only [ite_mul,zero_mul,Fintype.sum_ite_eq]
  exact hM.1 i j

omit [Fintype V] [DecidableEq A] in
lemma mul_blockProjection (E:BasedComplex Q (K:=K) I) (T:Set I)
    {J:Type*} (p:J → GeneratorPlacement V) (M:Matrix J I (Q.Zigzag K))
    (hM:ProjectiveEntries Q p E.placement M) :
    M*blockProjection Q E T=M.submatrix id Subtype.val := by
  apply Matrix.ext
  intro i j
  change (∑ k,M i k*(if k=(j:I) then vertexId Q (K:=K) (E.placement k).color else 0))=M i j
  simp only [mul_ite,MulZeroClass.mul_zero,Fintype.sum_ite_eq']
  exact hM.2 i j

omit [Fintype V] [DecidableEq A] in
lemma block_inclusion_projection (E:BasedComplex Q (K:=K) I) (T:Set I) :
    blockInclusion Q E T*blockProjection Q E T=projectiveIdentity Q (fun i:T=>E.placement i) := by
  rw [blockInclusion_mul Q E T _ _ (blockProjection_entries Q E T)]
  apply Matrix.ext
  intro i j
  change (if (i:I)=(j:I) then vertexId Q (K:=K) (E.placement i).color else 0)=
    (if i=j then vertexId Q (K:=K) (E.placement i).color else 0)
  simp only [Subtype.val_inj]

omit [Fintype V] [DecidableEq A] in
lemma blockInclusion_commute (E:BasedComplex Q (K:=K) I) (T:Set I) (h:BlockClosed Q E T) :
    (blockRestriction Q E T h).differential*blockInclusion Q E T=
      blockInclusion Q E T*E.differential := by
  rw [blockInclusion_mul Q E T _ _ E.entries]
  apply Matrix.ext
  intro i j
  change (∑ k:T,E.differential i k*(if (k:I)=j then vertexId Q (K:=K) (E.placement k).color else 0))=E.differential i j
  by_cases hj:j∈T
  · let j':T:=⟨j,hj⟩
    have he (k:T) : ((k:I)=j) ↔ k=j' := by simp only [j',Subtype.ext_iff]
    simp only [he,mul_ite,MulZeroClass.mul_zero,Fintype.sum_ite_eq']
    exact E.entries.2 i j
  · have hz:E.differential i j=0 := by
      by_contra hh
      exact hj ((h i j hh).mp i.property)
    rw [hz]
    apply Finset.sum_eq_zero
    intro k _
    have hne:(k:I)≠j := by intro he; exact hj (he ▸ k.property)
    rw [ite_eq_right hne,MulZeroClass.mul_zero]

omit [Fintype V] [DecidableEq A] in
lemma blockProjection_commute (E:BasedComplex Q (K:=K) I) (T:Set I) (h:BlockClosed Q E T) :
    E.differential*blockProjection Q E T=
      blockProjection Q E T*(blockRestriction Q E T h).differential := by
  rw [mul_blockProjection Q E T _ _ E.entries]
  apply Matrix.ext
  intro i j
  change E.differential i j=(∑ k:T,(if i=(k:I) then vertexId Q (K:=K) (E.placement i).color else 0)*E.differential k j)
  by_cases hi:i∈T
  · let i':T:=⟨i,hi⟩
    have he (k:T) : (i=(k:I)) ↔ i'=k := by simp only [i',Subtype.ext_iff]
    simp only [he,ite_mul,zero_mul,Fintype.sum_ite_eq]
    exact (E.entries.1 i j).symm
  · have hz:E.differential i j=0 := by
      by_contra hh
      exact hi ((h i j hh).mpr j.property)
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro k _
    have hne:i≠(k:I) := by intro he; exact hi (he.symm ▸ k.property)
    rw [ite_eq_right hne,zero_mul]

noncomputable def blockInclusionMap (E:BasedComplex Q (K:=K) I) (T:Set I) (h:BlockClosed Q E T) :
    Map Q (blockRestriction Q E T h) E where
  matrix:=blockInclusion Q E T
  entries:=blockInclusion_entries Q E T
  degree:=fun i j=>mapDegree_identity Q (i:I) j
  commute:=blockInclusion_commute Q E T h

noncomputable def blockProjectionMap (E:BasedComplex Q (K:=K) I) (T:Set I) (h:BlockClosed Q E T) :
    Map Q E (blockRestriction Q E T h) where
  matrix:=blockProjection Q E T
  entries:=blockProjection_entries Q E T
  degree:=fun i j=>mapDegree_identity Q i (j:I)
  commute:=blockProjection_commute Q E T h

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
