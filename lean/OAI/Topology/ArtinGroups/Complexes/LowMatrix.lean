import Mathlib
import OAI.Topology.ArtinGroups.Quivers.Level
import OAI.Topology.ArtinGroups.Complexes.DownClosed

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J L:Type u} [Fintype I] [Fintype J] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq L]
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

noncomputable def lowMatrix (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (M:Matrix I J (Q.Zigzag K)) (d:ℤ) :
    Matrix (lowerLevelSet Q E d) (lowerLevelSet Q F d) (Q.Zigzag K) :=
  fun i j=>M i j

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] [DecidableEq L] in
lemma lowMatrix_mul (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (G:BasedComplex Q (K:=K) L) (M:Matrix I J (Q.Zigzag K))
    (N:Matrix J L (Q.Zigzag K)) (d:ℤ)
    (hM:∀ i j,M i j≠0→(F.placement j).level≤(E.placement i).level) :
    lowMatrix Q E G (M*N) d=lowMatrix Q E F M d*lowMatrix Q F G N d := by
  apply Matrix.ext
  intro i k
  change (∑ j,M i j*N j k)=∑ j:lowerLevelSet Q F d,M i j*N j k
  symm
  apply Fintype.sum_of_injective (Subtype.val:lowerLevelSet Q F d→J) Subtype.val_injective
  · intro j hj
    have hz:M i j=0 := by
      by_contra hn
      have hi:(E.placement i).level≤d:=i.property
      exact hj ⟨⟨j,le_trans (hM i j hn) hi⟩,rfl⟩
    rw [hz,zero_mul]
  · intro j; rfl

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma lowMatrix_add (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (M N:Matrix I J (Q.Zigzag K)) (d:ℤ) :
    lowMatrix Q E F (M+N) d=lowMatrix Q E F M d+lowMatrix Q E F N d := rfl

omit [Fintype V] [DecidableEq A] in
lemma lowMatrix_identity (E:BasedComplex Q (K:=K) I) (d:ℤ) :
    lowMatrix Q E E (projectiveIdentity Q E.placement) d=
      projectiveIdentity Q (fun i:lowerLevelSet Q E d=>E.placement i) := by
  apply Matrix.ext; intro i j
  change (if (i:I)=(j:I) then vertexId Q (K:=K) (E.placement i).color else 0)=
    (if i=j then vertexId Q (K:=K) (E.placement i).color else 0)
  simp only [Subtype.val_inj]

noncomputable def Map.lowerTruncation {E:BasedComplex Q (K:=K) I}
    {F:BasedComplex Q (K:=K) J} (f:Map Q E F)
    (hE:E.IsMinimal Q) (hF:F.IsMinimal Q) (d:ℤ) :
    Map Q (lowerTruncation Q E hE d) (lowerTruncation Q F hF d) where
  matrix:=lowMatrix Q E F f.matrix d
  entries:=⟨fun i j=>f.entries.1 i j,fun i j=>f.entries.2 i j⟩
  degree:=fun i j=>f.degree i j
  commute:=by
    change lowMatrix Q E E E.differential d*lowMatrix Q E F f.matrix d=
      lowMatrix Q E F f.matrix d*lowMatrix Q F F F.differential d
    rw [← lowMatrix_mul Q E E F _ _ d (minimal_differential_level_bound Q E hE),
      ← lowMatrix_mul Q E F F _ _ d (map_level_bound Q f), f.commute]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma homotopy_level_bound (E:BasedComplex Q (K:=K) I)
    (H:Matrix I I (Q.Zigzag K)) (hH:MapDegree Q E.placement E.placement (-1) 0 H)
    (i j:I) (h:H i j≠0) : (E.placement j).level≤(E.placement i).level := by
  have hh:=mapDegree_level_bound Q hH h
  omega

noncomputable def HomotopyEquivalence.lowerTruncation
    {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (e:HomotopyEquivalence Q E F) (hE:E.IsMinimal Q) (hF:F.IsMinimal Q) (d:ℤ) :
    HomotopyEquivalence Q (lowerTruncation Q E hE d) (lowerTruncation Q F hF d) where
  forward:=e.forward.lowerTruncation Q hE hF d
  backward:=e.backward.lowerTruncation Q hF hE d
  sourceHomotopy:=lowMatrix Q E E e.sourceHomotopy d
  targetHomotopy:=lowMatrix Q F F e.targetHomotopy d
  sourceEntries:=⟨fun i j=>e.sourceEntries.1 i j,fun i j=>e.sourceEntries.2 i j⟩
  targetEntries:=⟨fun i j=>e.targetEntries.1 i j,fun i j=>e.targetEntries.2 i j⟩
  sourceDegree:=fun i j=>e.sourceDegree i j
  targetDegree:=fun i j=>e.targetDegree i j
  sourceEquation:=by
    change lowMatrix Q E F e.forward.matrix d*lowMatrix Q F E e.backward.matrix d=
      projectiveIdentity Q _+(lowMatrix Q E E E.differential d*lowMatrix Q E E e.sourceHomotopy d+
        lowMatrix Q E E e.sourceHomotopy d*lowMatrix Q E E E.differential d)
    rw [← lowMatrix_mul Q E F E _ _ d (map_level_bound Q e.forward),e.sourceEquation,
      lowMatrix_add,lowMatrix_identity,lowMatrix_add,
      lowMatrix_mul Q E E E _ _ d (minimal_differential_level_bound Q E hE),
      lowMatrix_mul Q E E E _ _ d (homotopy_level_bound Q E _ e.sourceDegree)]
    rfl
  targetEquation:=by
    change lowMatrix Q F E e.backward.matrix d*lowMatrix Q E F e.forward.matrix d=
      projectiveIdentity Q _+(lowMatrix Q F F F.differential d*lowMatrix Q F F e.targetHomotopy d+
        lowMatrix Q F F e.targetHomotopy d*lowMatrix Q F F F.differential d)
    rw [← lowMatrix_mul Q F E F _ _ d (map_level_bound Q e.backward),e.targetEquation,
      lowMatrix_add,lowMatrix_identity,lowMatrix_add,
      lowMatrix_mul Q F F F _ _ d (minimal_differential_level_bound Q F hF),
      lowMatrix_mul Q F F F _ _ d (homotopy_level_bound Q F _ e.targetDegree)]
    rfl

omit [Fintype V] [DecidableEq A] in
lemma lowInclusion_natural {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (f:Map Q E F) (hE:E.IsMinimal Q) (hF:F.IsMinimal Q) (d:ℤ) :
    (f.lowerTruncation Q hE hF d).matrix *
      (lowInclusion Q F (lowerLevelSet Q F d) (levelDownClosed Q F hF d)).matrix=
    (lowInclusion Q E (lowerLevelSet Q E d) (levelDownClosed Q E hE d)).matrix*f.matrix := by
  change lowMatrix Q E F f.matrix d * blockInclusion Q F (lowerLevelSet Q F d)=
    blockInclusion Q E (lowerLevelSet Q E d)*f.matrix
  rw [blockInclusion_mul Q E (lowerLevelSet Q E d) _ _ f.entries]
  apply Matrix.ext
  intro i j
  change (∑ k:lowerLevelSet Q F d,f.matrix i k*
    (if (k:J)=j then vertexId Q (K:=K) (F.placement k).color else 0))=f.matrix i j
  by_cases hj:j∈lowerLevelSet Q F d
  · let j':lowerLevelSet Q F d:=⟨j,hj⟩
    have he (k:lowerLevelSet Q F d) : ((k:J)=j)↔k=j' := by simp only [j',Subtype.ext_iff]
    simp only [he,mul_ite,MulZeroClass.mul_zero,Fintype.sum_ite_eq']
    exact f.entries.2 i j
  · have hz:f.matrix i j=0 := by
      by_contra hn
      exact hj (le_trans (map_level_bound Q f i j hn) i.property)
    rw [hz]
    apply Finset.sum_eq_zero
    intro k _
    have hn:(k:J)≠j:=fun he=>hj (he ▸ k.property)
    rw [ite_eq_right hn,MulZeroClass.mul_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
