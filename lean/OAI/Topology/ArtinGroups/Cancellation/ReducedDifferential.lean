import Mathlib
import OAI.Topology.ArtinGroups.Quivers.Reduction
import OAI.Topology.ArtinGroups.Cancellation.BlockPivot

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BlockPivot

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]
  {E : BasedComplex Q (K := K) (J ⊕ J ⊕ I)} (p : BlockPivot Q E)

noncomputable def reducedDifferential : Matrix (J ⊕ J ⊕ I) (J ⊕ J ⊕ I) (Q.Zigzag K) :=
  p.remainder Q * E.differential

lemma reducedDifferential_entries :
    ProjectiveEntries Q E.placement E.placement (p.reducedDifferential Q) :=
  projectiveEntries_mul Q (p.remainder_entries Q) E.entries

lemma reducedDifferential_degree :
    MapDegree Q E.placement E.placement 1 0 (p.reducedDifferential Q) := by
  exact mapDegree_mul Q (p.remainder_degree Q) E.degree

lemma reducedDifferential_square : p.reducedDifferential Q * p.reducedDifferential Q = 0 :=
  GaussianCancellation.cornerReduced_square _ _ _
    (projectiveIdentity_mul Q E.entries) (mul_projectiveIdentity Q E.entries) E.square_zero

lemma reducedDifferential_source_row (i : J) (k : J ⊕ J ⊕ I) :
    p.reducedDifferential Q (.inl i) k = 0 := by
  change (∑ j, p.remainder Q (.inl i) j * E.differential j k) = 0
  simp only [p.remainder_source_row Q, MulZeroClass.zero_mul, Finset.sum_const_zero]

lemma reducedDifferential_target_column (k : J ⊕ J ⊕ I) (j : J) :
    p.reducedDifferential Q k (.inr (.inl j)) = 0 := by
  unfold reducedDifferential
  rw [p.remainder_commutes Q]
  change (∑ l, E.differential k l * p.remainder Q l (.inr (.inl j))) = 0
  simp only [p.remainder_target_column Q, MulZeroClass.mul_zero, Finset.sum_const_zero]

lemma remainder_mul_reduced : p.remainder Q * p.reducedDifferential Q = p.reducedDifferential Q := by
  unfold reducedDifferential
  rw [← _root_.mul_assoc, p.remainder_square Q]

lemma reduced_mul_remainder : p.reducedDifferential Q * p.remainder Q = p.reducedDifferential Q := by
  unfold reducedDifferential
  rw [_root_.mul_assoc, ← p.remainder_commutes Q, ← _root_.mul_assoc, p.remainder_square Q]

noncomputable def reduced : BasedComplex Q (K := K) I where
  placement := fun i => E.placement (.inr (.inr i))
  differential := fun i j => p.reducedDifferential Q (.inr (.inr i)) (.inr (.inr j))
  entries := ⟨fun i j => (p.reducedDifferential_entries Q).1 _ _,
    fun i j => (p.reducedDifferential_entries Q).2 _ _⟩
  degree := fun i j => p.reducedDifferential_degree Q _ _
  square_zero := by
    apply Matrix.ext
    intro i j
    change (∑ k : I,
      p.reducedDifferential Q (.inr (.inr i)) (.inr (.inr k)) *
        p.reducedDifferential Q (.inr (.inr k)) (.inr (.inr j))) = 0
    rw [retained_sum Q _ _ (p.reducedDifferential_target_column Q)
      (p.reducedDifferential_source_row Q), p.reducedDifferential_square Q]
    rfl

noncomputable def reductionMap : Map Q E (p.reduced Q) where
  matrix := fun i j => p.remainder Q i (.inr (.inr j))
  entries := ⟨fun i j => (p.remainder_entries Q).1 _ _,
    fun i j => (p.remainder_entries Q).2 _ _⟩
  degree := fun i j => p.remainder_degree Q _ _
  commute := by
    apply Matrix.ext
    intro i j
    change (E.differential * p.remainder Q) i (.inr (.inr j)) =
      ∑ k : I, p.remainder Q i (.inr (.inr k)) *
        p.reducedDifferential Q (.inr (.inr k)) (.inr (.inr j))
    rw [retained_sum Q _ _ (p.remainder_target_column Q)
      (p.reducedDifferential_source_row Q), p.remainder_mul_reduced Q,
      ← p.remainder_commutes Q]
    rfl

noncomputable def inclusionMap : Map Q (p.reduced Q) E where
  matrix := fun i j => p.remainder Q (.inr (.inr i)) j
  entries := ⟨fun i j => (p.remainder_entries Q).1 _ _,
    fun i j => (p.remainder_entries Q).2 _ _⟩
  degree := fun i j => p.remainder_degree Q _ _
  commute := by
    apply Matrix.ext
    intro i j
    change (∑ k : I, p.reducedDifferential Q (.inr (.inr i)) (.inr (.inr k)) *
      p.remainder Q (.inr (.inr k)) j) =
      (p.remainder Q * E.differential) (.inr (.inr i)) j
    rw [retained_sum Q _ _ (p.reducedDifferential_target_column Q)
      (p.remainder_source_row Q), p.reduced_mul_remainder Q]
    rfl

lemma reduction_inclusion :
    (p.reductionMap Q).matrix * (p.inclusionMap Q).matrix = p.remainder Q := by
  apply Matrix.ext
  intro i j
  change (∑ k : I, p.remainder Q i (.inr (.inr k)) *
    p.remainder Q (.inr (.inr k)) j) = p.remainder Q i j
  rw [retained_sum Q _ _ (p.remainder_target_column Q)
    (p.remainder_source_row Q), p.remainder_square Q]

lemma inclusion_reduction :
    (p.inclusionMap Q).matrix * (p.reductionMap Q).matrix =
      projectiveIdentity Q (p.reduced Q).placement := by
  apply Matrix.ext
  intro i j
  change (p.remainder Q * p.remainder Q) (.inr (.inr i)) (.inr (.inr j)) = _
  rw [p.remainder_square Q, p.remainder_retained Q]
  rfl

noncomputable def reductionEquivalence : HomotopyEquivalence Q E (p.reduced Q) where
  forward := p.reductionMap Q
  backward := p.inclusionMap Q
  sourceHomotopy := -p.homotopy Q
  targetHomotopy := 0
  sourceEntries := projectiveEntries_neg Q (p.homotopy_entries Q)
  targetEntries := projectiveEntries_zero Q
  sourceDegree := mapDegree_neg Q (p.homotopy_degree Q)
  targetDegree := mapDegree_zero Q (-1) 0
  sourceEquation := by
    rw [p.reduction_inclusion Q]
    exact GaussianCancellation.cornerRemainder_homotopy _ _ _
  targetEquation := by
    rw [p.inclusion_reduction Q, Matrix.mul_zero, Matrix.zero_mul, add_zero, add_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BlockPivot

end OAI
