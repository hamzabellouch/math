import Mathlib
import OAI.Topology.ArtinGroups.Quivers.Reduction
import OAI.Topology.ArtinGroups.Cancellation.ScalarPivot

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ScalarPivot

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V] [Fintype I] [DecidableEq I]
  {E : BasedComplex Q (K := K) I} (p : ScalarPivot Q E)

abbrev Retained := {k : I // k ≠ p.source ∧ k ≠ p.target}

lemma retained_sum {X Y : Type*} (U : Matrix X I (Q.Zigzag K))
    (V : Matrix I Y (Q.Zigzag K)) (hU : ∀ i, U i p.target = 0)
    (hV : ∀ j, V p.source j = 0) (i : X) (j : Y) :
    (∑ k : p.Retained Q, U i k * V k j) = (U * V) i j := by
  apply Fintype.sum_of_injective (Subtype.val : p.Retained Q → I) Subtype.val_injective
  · intro k hk
    change U i k * V k j = 0
    by_cases hs : k = p.source
    · subst k
      rw [hV, MulZeroClass.mul_zero]
    · by_cases ht : k = p.target
      · subst k
        rw [hU, MulZeroClass.zero_mul]
      · exact (hk ⟨⟨k, hs, ht⟩, rfl⟩).elim
  · intro k
    rfl

noncomputable def reducedDifferential : Matrix I I (Q.Zigzag K) :=
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

lemma reducedDifferential_source_row (k : I) : p.reducedDifferential Q p.source k = 0 := by
  change (∑ j, p.remainder Q p.source j * E.differential j k) = 0
  simp only [p.remainder_source_row Q, MulZeroClass.zero_mul, Finset.sum_const_zero]

lemma reducedDifferential_target_column (k : I) : p.reducedDifferential Q k p.target = 0 := by
  unfold reducedDifferential
  rw [p.remainder_commutes Q]
  change (∑ j, E.differential k j * p.remainder Q j p.target) = 0
  simp only [p.remainder_target_column Q, MulZeroClass.mul_zero, Finset.sum_const_zero]

lemma remainder_mul_reduced : p.remainder Q * p.reducedDifferential Q = p.reducedDifferential Q := by
  unfold reducedDifferential
  rw [← _root_.mul_assoc, p.remainder_square Q]

lemma reduced_mul_remainder : p.reducedDifferential Q * p.remainder Q = p.reducedDifferential Q := by
  unfold reducedDifferential
  rw [_root_.mul_assoc, ← p.remainder_commutes Q, ← _root_.mul_assoc, p.remainder_square Q]

noncomputable def reduced : BasedComplex Q (K := K) (p.Retained Q) where
  placement := fun i => E.placement i
  differential := fun i j => p.reducedDifferential Q i j
  entries := ⟨fun i j => (p.reducedDifferential_entries Q).1 i j,
    fun i j => (p.reducedDifferential_entries Q).2 i j⟩
  degree := fun i j => p.reducedDifferential_degree Q i j
  square_zero := by
    apply Matrix.ext
    intro i j
    change (∑ k : p.Retained Q,
      p.reducedDifferential Q i k * p.reducedDifferential Q k j) = 0
    rw [p.retained_sum Q _ _ (p.reducedDifferential_target_column Q)
      (p.reducedDifferential_source_row Q), p.reducedDifferential_square Q]
    rfl

noncomputable def reductionMap : Map Q E (p.reduced Q) where
  matrix := fun i j => p.remainder Q i j
  entries := ⟨fun i j => (p.remainder_entries Q).1 i j,
    fun i j => (p.remainder_entries Q).2 i j⟩
  degree := fun i j => p.remainder_degree Q i j
  commute := by
    apply Matrix.ext
    intro i j
    change (E.differential * p.remainder Q) i j =
      ∑ k : p.Retained Q, p.remainder Q i k * p.reducedDifferential Q k j
    rw [p.retained_sum Q _ _ (p.remainder_target_column Q)
      (p.reducedDifferential_source_row Q), p.remainder_mul_reduced Q,
      ← p.remainder_commutes Q]
    rfl

noncomputable def inclusionMap : Map Q (p.reduced Q) E where
  matrix := fun i j => p.remainder Q i j
  entries := ⟨fun i j => (p.remainder_entries Q).1 i j,
    fun i j => (p.remainder_entries Q).2 i j⟩
  degree := fun i j => p.remainder_degree Q i j
  commute := by
    apply Matrix.ext
    intro i j
    change (∑ k : p.Retained Q, p.reducedDifferential Q i k * p.remainder Q k j) =
      (p.remainder Q * E.differential) i j
    rw [p.retained_sum Q _ _ (p.reducedDifferential_target_column Q)
      (p.remainder_source_row Q), p.reduced_mul_remainder Q]
    rfl

lemma reduction_inclusion :
    (p.reductionMap Q).matrix * (p.inclusionMap Q).matrix = p.remainder Q := by
  apply Matrix.ext
  intro i j
  change (∑ k : p.Retained Q, p.remainder Q i k * p.remainder Q k j) = p.remainder Q i j
  rw [p.retained_sum Q _ _ (p.remainder_target_column Q)
    (p.remainder_source_row Q), p.remainder_square Q]

lemma inclusion_reduction :
    (p.inclusionMap Q).matrix * (p.reductionMap Q).matrix =
      projectiveIdentity Q (p.reduced Q).placement := by
  apply Matrix.ext
  intro i j
  change (p.remainder Q * p.remainder Q) i j = _
  rw [p.remainder_square Q, p.remainder_retained Q i j i.property.2 j.property.1]
  change (Matrix.diagonal (fun k => vertexId Q (E.placement k).color)) i.val j.val =
    (Matrix.diagonal (fun k : p.Retained Q => vertexId Q (E.placement k).color)) i j
  by_cases h : i = j
  · subst j
    simp
  · have hv : i.val ≠ j.val := fun he => h (Subtype.ext he)
    simp [Matrix.diagonal, h, hv]

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

lemma retained_card_lt : Fintype.card (p.Retained Q) < Fintype.card I := by
  apply Fintype.card_lt_of_injective_not_surjective (Subtype.val : p.Retained Q → I)
    Subtype.val_injective
  intro h
  obtain ⟨k, hk⟩ := h p.source
  exact k.property.1 hk

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ScalarPivot

end OAI
