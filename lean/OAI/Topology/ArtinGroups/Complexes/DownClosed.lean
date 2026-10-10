import Mathlib
import OAI.Topology.ArtinGroups.Quivers.OrthogonalVertices
import OAI.Topology.ArtinGroups.Cancellation.ReducedDifferential2
import OAI.Topology.ArtinGroups.Complexes.BlockClosed
import OAI.Topology.ArtinGroups.Complexes.Identity

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

def DownClosed (E:BasedComplex Q (K:=K) I) (T:Set I) : Prop :=
  ∀ i∈T,∀ j,E.differential i j≠0→j∈T

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma DownClosed.low_condition {E:BasedComplex Q (K:=K) I} {T:Set I}
    (h:DownClosed Q E T) : ∀ i∈T,∀ j∈T,∀ k∉T,E.differential i k*E.differential k j=0 := by
  intro i hi j _ k hk
  have hz:E.differential i k=0 := Classical.not_not.mp (fun hn=>hk (h i hi k hn))
  rw [hz,zero_mul]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma DownClosed.high_condition {E:BasedComplex Q (K:=K) I} {T:Set I}
    (h:DownClosed Q E T) : ∀ i∈Tᶜ,∀ j∈Tᶜ,∀ k∉Tᶜ,E.differential i k*E.differential k j=0 := by
  intro i _ j hj k hk
  have hk':k∈T:=Classical.not_not.mp hk
  have hz:E.differential k j=0 := Classical.not_not.mp (fun hn=>hj (h k hk' j hn))
  rw [hz,MulZeroClass.mul_zero]

noncomputable def lowRestriction (E:BasedComplex Q (K:=K) I) (T:Set I) (h:DownClosed Q E T) :
    BasedComplex Q (K:=K) T := E.restrict Q T h.low_condition
noncomputable def highRestriction (E:BasedComplex Q (K:=K) I) (T:Set I) (h:DownClosed Q E T) :
    BasedComplex Q (K:=K) (Tᶜ:Set I) := E.restrict Q Tᶜ h.high_condition

omit [Fintype V] [DecidableEq A] in
lemma lowInclusion_commute (E:BasedComplex Q (K:=K) I) (T:Set I) (h:DownClosed Q E T) :
    (lowRestriction Q E T h).differential*blockInclusion Q E T=
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
  · have hz:E.differential i j=0 := Classical.not_not.mp (fun hh=>hj (h i i.property j hh))
    rw [hz]
    apply Finset.sum_eq_zero
    intro k _
    have hne:(k:I)≠j := by intro he; exact hj (he ▸ k.property)
    rw [ite_eq_right hne,MulZeroClass.mul_zero]

omit [Fintype V] [DecidableEq A] in
lemma highProjection_commute (E:BasedComplex Q (K:=K) I) (T:Set I) (h:DownClosed Q E T) :
    E.differential*blockProjection Q E Tᶜ=
      blockProjection Q E Tᶜ*(highRestriction Q E T h).differential := by
  rw [mul_blockProjection Q E Tᶜ _ _ E.entries]
  apply Matrix.ext
  intro i j
  change E.differential i j=(∑ k:(Tᶜ:Set I),(if i=(k:I) then vertexId Q (K:=K) (E.placement i).color else 0)*E.differential k j)
  by_cases hi:i∈Tᶜ
  · let i':(Tᶜ:Set I):=⟨i,hi⟩
    have he (k:(Tᶜ:Set I)) : (i=(k:I)) ↔ i'=k := by simp only [i',Subtype.ext_iff]
    simp only [he,ite_mul,zero_mul,Fintype.sum_ite_eq]
    exact (E.entries.1 i j).symm
  · have hi':i∈T:=Classical.not_not.mp hi
    have hz:E.differential i j=0 := Classical.not_not.mp (fun hh=>j.property (h i hi' j hh))
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro k _
    have hne:i≠(k:I) := by intro he; exact hi (he.symm ▸ k.property)
    rw [ite_eq_right hne,zero_mul]

noncomputable def lowInclusion (E:BasedComplex Q (K:=K) I) (T:Set I) (h:DownClosed Q E T) :
    Map Q (lowRestriction Q E T h) E where
  matrix:=blockInclusion Q E T
  entries:=blockInclusion_entries Q E T
  degree:=fun i j=>mapDegree_identity Q (i:I) j
  commute:=lowInclusion_commute Q E T h

noncomputable def highProjection (E:BasedComplex Q (K:=K) I) (T:Set I) (h:DownClosed Q E T) :
    Map Q E (highRestriction Q E T h) where
  matrix:=blockProjection Q E Tᶜ
  entries:=blockProjection_entries Q E Tᶜ
  degree:=fun i j=>mapDegree_identity Q i (j:I)
  commute:=highProjection_commute Q E T h

def lowerLevelSet (E:BasedComplex Q (K:=K) I) (d:ℤ) : Set I := {i|(E.placement i).level≤d}

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma levelDownClosed (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (d:ℤ) :
    DownClosed Q E (lowerLevelSet Q E d) := by
  intro i hi j hij
  have h:=differential_level Q E hE hij
  change (E.placement j).level≤d
  change (E.placement i).level≤d at hi
  rcases h with h|h <;> omega

noncomputable def lowerTruncation (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (d:ℤ) :=
  lowRestriction Q E (lowerLevelSet Q E d) (levelDownClosed Q E hE d)
noncomputable def upperTruncation (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (d:ℤ) :=
  highRestriction Q E (lowerLevelSet Q E d) (levelDownClosed Q E hE d)

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma lowerTruncation_minimal (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (d:ℤ) :
    (lowerTruncation Q E hE d).IsMinimal Q := fun i j=>hE i j
omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma upperTruncation_minimal (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (d:ℤ) :
    (upperTruncation Q E hE d).IsMinimal Q := fun i j=>hE i j

noncomputable def lowConeNormalized (E:BasedComplex Q (K:=K) I) (T:Set I) (h:DownClosed Q E T) :=
  ((lowInclusion Q E T h).cone Q).reindex Q (Equiv.sumCongr (Equiv.refl T) (Equiv.Set.sumCompl T))

noncomputable def lowConePivot (E:BasedComplex Q (K:=K) I) (T:Set I) (h:DownClosed Q E T) :
    BlockPivot Q (lowConeNormalized Q E T h) where
  coefficient:=1
  nonzero:=one_ne_zero
  color _:=rfl
  cochain i:=by change (E.placement i).cochain=(E.placement i).cochain-1+1; omega
  internal _:=rfl
  entry i j:=by
    change (if (i:I)=(j:I) then vertexId Q (K:=K) (E.placement i).color else 0)=
      1 • (if i=j then vertexId Q (K:=K) (E.placement i).color else 0)
    simp only [one_smul,Subtype.val_inj]

omit [Fintype V] [DecidableEq A] in
lemma lowCone_source_retained (E:BasedComplex Q (K:=K) I) (T:Set I) (h:DownClosed Q E T)
    (i:T) (j:(Tᶜ:Set I)) : (lowConeNormalized Q E T h).differential (.inl i) (.inr (.inr j))=0 := by
  change (if (i:I)=(j:I) then vertexId Q (K:=K) (E.placement i).color else 0)=0
  have hn:(i:I)≠(j:I):=fun he=>j.property (he ▸ i.property)
  rw [ite_eq_right hn]

omit [Fintype V] [DecidableEq A] in
lemma lowCone_reduced_eq (E:BasedComplex Q (K:=K) I) (T:Set I) (h:DownClosed Q E T) :
    (lowConePivot Q E T h).reduced Q=highRestriction Q E T h := by
  apply ext_placement_differential Q
  · rfl
  · apply Matrix.ext
    intro i j
    rw [BlockPivot.reduced_differential]
    simp only [lowCone_source_retained,MulZeroClass.mul_zero,Finset.sum_const_zero,sub_zero]
    rfl

noncomputable def lowConeReduction (E:BasedComplex Q (K:=K) I) (T:Set I) (h:DownClosed Q E T) :
    HomotopyEquivalence Q ((lowInclusion Q E T h).cone Q) (highRestriction Q E T h) := by
  have e:=(((lowInclusion Q E T h).cone Q).reindexHomotopyEquivalence Q
    (Equiv.sumCongr (Equiv.refl T) (Equiv.Set.sumCompl T))).trans Q
      ((lowConePivot Q E T h).reductionEquivalence Q)
  rw [lowCone_reduced_eq] at e
  exact e

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
