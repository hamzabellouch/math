import Mathlib
import OAI.Topology.ArtinGroups.Cancellation.ScalarPivot

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

structure BlockPivot (E : BasedComplex Q (K := K) (J ⊕ J ⊕ I)) where
  coefficient : K
  nonzero : coefficient ≠ 0
  color : ∀ j, (E.placement (.inr (.inl j))).color = (E.placement (.inl j)).color
  cochain : ∀ j, (E.placement (.inr (.inl j))).cochain =
    (E.placement (.inl j)).cochain + 1
  internal : ∀ j, (E.placement (.inr (.inl j))).internal =
    (E.placement (.inl j)).internal
  entry : ∀ i j, E.differential (.inl i) (.inr (.inl j)) =
    coefficient • projectiveIdentity Q (fun j => E.placement (.inl j)) i j

namespace BlockPivot

variable {E : BasedComplex Q (K := K) (J ⊕ J ⊕ I)} (p : BlockPivot Q E)

noncomputable def homotopy : Matrix (J ⊕ J ⊕ I) (J ⊕ J ⊕ I) (Q.Zigzag K)
  | .inr (.inl i), .inl j =>
      p.coefficient⁻¹ • projectiveIdentity Q (fun j => E.placement (.inl j)) i j
  | _, _ => 0

omit [DecidableEq I] in
lemma homotopy_entries : ProjectiveEntries Q E.placement E.placement (p.homotopy Q) := by
  constructor
  · intro i j
    rcases i with i | i | i <;> rcases j with j | j | j
    all_goals try exact MulZeroClass.mul_zero _
    change vertexId Q (E.placement (.inr (.inl i))).color *
      (p.coefficient⁻¹ • projectiveIdentity Q (fun j => E.placement (.inl j)) i j) = _
    rw [p.color, mul_smul]
    exact congrArg (p.coefficient⁻¹ • ·)
      ((projectiveEntries_identity Q (p := fun j => E.placement (.inl j))).1 i j)
  · intro i j
    rcases i with i | i | i <;> rcases j with j | j | j
    all_goals try exact MulZeroClass.zero_mul _
    change (p.coefficient⁻¹ • projectiveIdentity Q (fun j => E.placement (.inl j)) i j) *
      vertexId Q (E.placement (.inl j)).color = _
    rw [smul_mul]
    exact congrArg (p.coefficient⁻¹ • ·)
      ((projectiveEntries_identity Q (p := fun j => E.placement (.inl j))).2 i j)

omit [DecidableEq I] in
lemma homotopy_degree : MapDegree Q E.placement E.placement (-1) 0 (p.homotopy Q) := by
  intro i j
  rcases i with i | i | i <;> rcases j with j | j | j
  all_goals try exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  by_cases hij : i = j
  · subst j
    change ( (E.placement (.inl i)).cochain ≠ (E.placement (.inr (.inl i))).cochain + -1 →
        p.coefficient⁻¹ • projectiveIdentity Q (fun j => E.placement (.inl j)) i i = 0) ∧ _
    refine ⟨fun h => (h (by rw [p.cochain]; omega)).elim, ?_⟩
    change Homogeneous Q (0 + (E.placement (.inr (.inl i))).internal -
      (E.placement (.inl i)).internal) (p.coefficient⁻¹ • projectiveIdentity Q
        (fun j => E.placement (.inl j)) i i)
    rw [p.internal]
    simp only [projectiveIdentity, Matrix.diagonal_apply, ite_true]
    simpa only [zero_add, sub_self] using homogeneous_smul Q (r := p.coefficient⁻¹)
      (hx := homogeneous_vertexId Q (K := K) (E.placement (.inl i)).color)
  · change (_ → p.coefficient⁻¹ • projectiveIdentity Q (fun j => E.placement (.inl j)) i j = 0) ∧ _
    change (_ → p.coefficient⁻¹ • projectiveIdentity Q (fun j => E.placement (.inl j)) i j = 0) ∧
      Homogeneous Q _ (p.coefficient⁻¹ • projectiveIdentity Q (fun j => E.placement (.inl j)) i j)
    rw [show projectiveIdentity Q (fun j => E.placement (.inl j)) i j = 0 by
      simp only [projectiveIdentity, Matrix.diagonal_apply, ite_eq_right hij], smul_zero]
    exact ⟨fun _ => rfl, homogeneous_zero Q _⟩

omit [DecidableEq I] in
lemma homotopy_mul {L : Type*} (M : Matrix (J ⊕ J ⊕ I) L (Q.Zigzag K))
    {q : L → GeneratorPlacement V} (hM : ProjectiveEntries Q E.placement q M)
    (i : J ⊕ J ⊕ I) (j : L) :
    (p.homotopy Q * M) i j = match i with
      | .inr (.inl k) => p.coefficient⁻¹ • M (.inl k) j
      | _ => 0 := by
  rcases i with i | i | i
  all_goals simp only [Matrix.mul_apply, Fintype.sum_sum_type, homotopy,
    MulZeroClass.zero_mul, Finset.sum_const_zero, add_zero]
  simp only [projectiveIdentity, Matrix.diagonal_apply, smul_ite, smul_zero,
    ite_mul, MulZeroClass.zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    smul_mul, hM.1]

omit [DecidableEq I] in
lemma mul_homotopy {L : Type*} [Fintype L]
    (M : Matrix L (J ⊕ J ⊕ I) (Q.Zigzag K))
    {q : L → GeneratorPlacement V} (hM : ProjectiveEntries Q q E.placement M)
    (i : L) (j : J ⊕ J ⊕ I) :
    (M * p.homotopy Q) i j = match j with
      | .inl k => p.coefficient⁻¹ • M i (.inr (.inl k))
      | _ => 0 := by
  rcases j with j | j | j
  all_goals simp only [Matrix.mul_apply, Fintype.sum_sum_type, homotopy,
    MulZeroClass.mul_zero, Finset.sum_const_zero, add_zero, zero_add]
  simp only [projectiveIdentity, Matrix.diagonal_apply, smul_ite, smul_zero,
    mul_ite, MulZeroClass.mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    mul_smul]
  rw [← p.color]
  exact congrArg (p.coefficient⁻¹ • ·) (hM.2 i (.inr (.inl j)))

omit [DecidableEq I] in
lemma homotopy_square : p.homotopy Q * p.homotopy Q = 0 := by
  apply Matrix.ext
  intro i j
  rw [p.homotopy_mul Q _ (p.homotopy_entries Q)]
  rcases i with i | i | i
  · rfl
  · exact smul_zero _
  · rfl

omit [DecidableEq I] in
lemma homotopy_retract : p.homotopy Q * E.differential * p.homotopy Q = p.homotopy Q := by
  apply Matrix.ext
  intro i j
  rw [p.mul_homotopy Q _ (projectiveEntries_mul Q (p.homotopy_entries Q) E.entries)]
  rcases j with j | j | j
  · change p.coefficient⁻¹ • (p.homotopy Q * E.differential) i (.inr (.inl j)) = _
    rw [p.homotopy_mul Q _ E.entries]
    rcases i with i | i | i
    · exact smul_zero _
    · dsimp only
      rw [p.entry]
      change p.coefficient⁻¹ • (p.coefficient⁻¹ • (p.coefficient • _)) = p.coefficient⁻¹ • _
      congr 1
      rw [smul_smul, inv_mul_cancel₀ p.nonzero, one_smul]
    · exact smul_zero _
  · rcases i with i | i | i <;> rfl
  · rcases i with i | i | i <;> rfl

noncomputable def remainder : Matrix (J ⊕ J ⊕ I) (J ⊕ J ⊕ I) (Q.Zigzag K) :=
  GaussianCancellation.cornerRemainder (projectiveIdentity Q E.placement)
    E.differential (p.homotopy Q)

lemma remainder_entries : ProjectiveEntries Q E.placement E.placement (p.remainder Q) := by
  unfold remainder GaussianCancellation.cornerRemainder
  simp only [sub_eq_add_neg]
  exact projectiveEntries_add Q
    (projectiveEntries_add Q (projectiveEntries_identity Q)
      (projectiveEntries_neg Q (projectiveEntries_mul Q E.entries (p.homotopy_entries Q))))
    (projectiveEntries_neg Q (projectiveEntries_mul Q (p.homotopy_entries Q) E.entries))

lemma remainder_degree : MapDegree Q E.placement E.placement 0 0 (p.remainder Q) := by
  have h₁ := mapDegree_mul Q E.degree (p.homotopy_degree Q)
  have h₂ := mapDegree_mul Q (p.homotopy_degree Q) E.degree
  norm_num at h₁ h₂
  unfold remainder GaussianCancellation.cornerRemainder
  simp only [sub_eq_add_neg]
  exact mapDegree_add Q (mapDegree_add Q (mapDegree_identity Q) (mapDegree_neg Q h₁))
    (mapDegree_neg Q h₂)

lemma remainder_commutes : p.remainder Q * E.differential = E.differential * p.remainder Q :=
  GaussianCancellation.cornerRemainder_commutes _ _ _
    (projectiveIdentity_mul Q E.entries) (mul_projectiveIdentity Q E.entries) E.square_zero

lemma remainder_square : p.remainder Q * p.remainder Q = p.remainder Q :=
  GaussianCancellation.cornerRemainder_idempotent _ _ _
    (projectiveIdentity_mul Q (projectiveEntries_identity Q))
    (projectiveIdentity_mul Q E.entries) (mul_projectiveIdentity Q E.entries)
    (projectiveIdentity_mul Q (p.homotopy_entries Q))
    (mul_projectiveIdentity Q (p.homotopy_entries Q))
    E.square_zero (p.homotopy_square Q) (p.homotopy_retract Q)

lemma remainder_source_row (i : J) (k : J ⊕ J ⊕ I) : p.remainder Q (.inl i) k = 0 := by
  change (projectiveIdentity Q E.placement) (.inl i) k -
      (E.differential * p.homotopy Q) (.inl i) k -
      (p.homotopy Q * E.differential) (.inl i) k = 0
  rw [p.homotopy_mul Q _ E.entries, sub_zero, p.mul_homotopy Q _ E.entries]
  rcases k with k | k | k
  · dsimp only
    rw [p.entry, smul_smul, inv_mul_cancel₀ p.nonzero, one_smul]
    simp only [projectiveIdentity, Matrix.diagonal_apply, Sum.inl.injEq, sub_self]
  · simp [projectiveIdentity]
  · simp [projectiveIdentity]

lemma remainder_target_column (k : J ⊕ J ⊕ I) (j : J) :
    p.remainder Q k (.inr (.inl j)) = 0 := by
  change (projectiveIdentity Q E.placement) k (.inr (.inl j)) -
      (E.differential * p.homotopy Q) k (.inr (.inl j)) -
      (p.homotopy Q * E.differential) k (.inr (.inl j)) = 0
  rw [p.mul_homotopy Q _ E.entries, sub_zero, p.homotopy_mul Q _ E.entries]
  rcases k with k | k | k
  · simp [projectiveIdentity]
  · dsimp only
    rw [p.entry, smul_smul, inv_mul_cancel₀ p.nonzero, one_smul]
    simp only [projectiveIdentity, Matrix.diagonal_apply, Sum.inr.injEq, Sum.inl.injEq]
    by_cases h : k = j
    · subst j
      simp only [ite_true, p.color, sub_self]
    · simp only [ite_eq_right h, sub_self]
  · simp [projectiveIdentity]

lemma remainder_retained (i j : I) : p.remainder Q (.inr (.inr i)) (.inr (.inr j)) =
    projectiveIdentity Q (fun k => E.placement (.inr (.inr k))) i j := by
  change (projectiveIdentity Q E.placement) (.inr (.inr i)) (.inr (.inr j)) -
      (E.differential * p.homotopy Q) (.inr (.inr i)) (.inr (.inr j)) -
      (p.homotopy Q * E.differential) (.inr (.inr i)) (.inr (.inr j)) = _
  rw [p.mul_homotopy Q _ E.entries, p.homotopy_mul Q _ E.entries]
  by_cases hij : i = j
  · subst j
    simp [projectiveIdentity]
  · simp [projectiveIdentity, hij]

omit [DecidableEq I] [DecidableEq J] in
lemma retained_sum {X Y : Type*} (U : Matrix X (J ⊕ J ⊕ I) (Q.Zigzag K))
    (M : Matrix (J ⊕ J ⊕ I) Y (Q.Zigzag K))
    (hU : ∀ i j, U i (.inr (.inl j)) = 0) (hM : ∀ i j, M (.inl i) j = 0)
    (i : X) (j : Y) :
    (∑ k : I, U i (.inr (.inr k)) * M (.inr (.inr k)) j) = (U * M) i j := by
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, hU, hM, MulZeroClass.mul_zero,
    MulZeroClass.zero_mul, Finset.sum_const_zero, zero_add]

end BlockPivot
end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
