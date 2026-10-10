import Mathlib
import OAI.Topology.ArtinGroups.Complexes.InverseTwistIndex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

def inverseTwistPlacement (E : BasedComplex Q (K := K) I) (α : V) :
    InverseTwistIndex Q E α → GeneratorPlacement V
  | .inl u => ⟨α, (E.placement u.1).cochain - 1,
      (E.placement u.1).internal + Path.length u.2.val⟩
  | .inr (.inl u) => ⟨α, (E.placement u.1).cochain,
      (E.placement u.1).internal + Path.length u.2.val - 2⟩
  | .inr (.inr (.inl u)) => testPlacement Q E.placement α u
  | .inr (.inr (.inr (.inl i))) => E.placement i
  | .inr (.inr (.inr (.inr u))) => ⟨α, (E.placement u.1).cochain + 1,
      (E.placement u.1).internal + Path.length u.2.val - 2⟩

omit [DecidableEq I] in
lemma normalizedInverseTwist_placement (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    (normalizedInverseTwist Q hn E α).placement = inverseTwistPlacement Q E α := by
  funext i
  rcases i with u | u | u | i | u
  · rfl
  · change (⟨α, (E.placement u.1).cochain + 1 - 1,
      (E.placement u.1).internal + Path.length u.2.val - 2 + 0⟩ : GeneratorPlacement V) = _
    simp only [add_sub_cancel_right, add_zero]
    rfl
  · change (⟨α, (E.placement u.1).cochain + 1 - 1,
      (E.placement u.1).internal + Path.length u.2.val - 2 + 2⟩ : GeneratorPlacement V) = _
    simp only [add_sub_cancel_right, sub_add_cancel]
    rfl
  · rfl
  · rfl

noncomputable def inverseTwistProjection (E : BasedComplex Q (K := K) I) (α : V) :
    Matrix (InverseTwistIndex Q E α) I (Q.Zigzag K)
  | .inr (.inr (.inl u)), j => evaluationMatrix Q E.placement α u j
  | .inr (.inr (.inr (.inl i))), j => projectiveIdentity Q E.placement i j
  | _, _ => 0

noncomputable def inverseTwistInjection (E : BasedComplex Q (K := K) I) (α : V) :
    Matrix I (InverseTwistIndex Q E α) (Q.Zigzag K)
  | i, .inr (.inl u) => -coevaluationMatrix Q E.placement α i u
  | i, .inr (.inr (.inr (.inl j))) => projectiveIdentity Q E.placement i j
  | _, _ => 0

noncomputable def inverseTwistHomotopy (E : BasedComplex Q (K := K) I) (α : V) :
    Matrix (InverseTwistIndex Q E α) (InverseTwistIndex Q E α) (Q.Zigzag K)
  | .inr (.inr (.inl u)), .inl v => projectiveIdentity Q (testPlacement Q E.placement α) u v
  | .inr (.inr (.inr (.inr u))), .inr (.inl v) =>
      -projectiveIdentity Q (testPlacement Q E.placement α) u v
  | _, _ => 0

lemma inverseTwistProjection_entries (E : BasedComplex Q (K := K) I) (α : V) :
    ProjectiveEntries Q (inverseTwistPlacement Q E α) E.placement
      (inverseTwistProjection Q E α) := by
  constructor
  · intro i j
    rcases i with u | u | u | i | u
    · exact MulZeroClass.mul_zero _
    · exact MulZeroClass.mul_zero _
    · exact (evaluation_entries Q E.placement α).1 u j
    · exact (projectiveEntries_identity Q).1 i j
    · exact MulZeroClass.mul_zero _
  · intro i j
    rcases i with u | u | u | i | u
    · exact MulZeroClass.zero_mul _
    · exact MulZeroClass.zero_mul _
    · exact (evaluation_entries Q E.placement α).2 u j
    · exact (projectiveEntries_identity Q).2 i j
    · exact MulZeroClass.zero_mul _

lemma inverseTwistProjection_degree (E : BasedComplex Q (K := K) I) (α : V) :
    MapDegree Q (inverseTwistPlacement Q E α) E.placement 0 0
      (inverseTwistProjection Q E α) := by
  intro i j
  rcases i with u | u | u | i | u
  · exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩
  · exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩
  · exact evaluation_degree Q E.placement α u j
  · exact mapDegree_identity Q i j
  · exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩

lemma inverseTwistInjection_entries (E : BasedComplex Q (K := K) I) (α : V) :
    ProjectiveEntries Q E.placement (inverseTwistPlacement Q E α)
      (inverseTwistInjection Q E α) := by
  constructor
  · intro i j
    rcases j with u | u | u | j | u
    · exact MulZeroClass.mul_zero _
    · exact (projectiveEntries_neg Q (coevaluation_entries Q E.placement α)).1 i u
    · exact MulZeroClass.mul_zero _
    · exact (projectiveEntries_identity Q).1 i j
    · exact MulZeroClass.mul_zero _
  · intro i j
    rcases j with u | u | u | j | u
    · exact MulZeroClass.zero_mul _
    · exact (projectiveEntries_neg Q (coevaluation_entries Q E.placement α)).2 i u
    · exact MulZeroClass.zero_mul _
    · exact (projectiveEntries_identity Q).2 i j
    · exact MulZeroClass.zero_mul _

lemma inverseTwistInjection_degree (E : BasedComplex Q (K := K) I) (α : V) :
    MapDegree Q E.placement (inverseTwistPlacement Q E α) 0 0
      (inverseTwistInjection Q E α) := by
  intro i j
  rcases j with u | u | u | j | u
  · exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩
  · exact mapDegree_neg Q (coevaluation_degree Q E.placement α) i u
  · exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩
  · exact mapDegree_identity Q i j
  · exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩

omit [Fintype V] in
omit [DecidableEq A] [DecidableEq I] in
lemma inverseTwistHomotopy_entries (E : BasedComplex Q (K := K) I) (α : V) :
    ProjectiveEntries Q (inverseTwistPlacement Q E α) (inverseTwistPlacement Q E α)
      (inverseTwistHomotopy Q E α) := by
  constructor
  · intro i j
    rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v
    all_goals first
      | exact MulZeroClass.mul_zero _
      | exact (projectiveEntries_identity Q (K := K)
          (p := testPlacement Q E.placement α)).1 u v
      | exact (projectiveEntries_neg Q (projectiveEntries_identity Q (K := K)
          (p := testPlacement Q E.placement α))).1 u v
  · intro i j
    rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v
    all_goals first
      | exact MulZeroClass.zero_mul _
      | exact (projectiveEntries_identity Q (K := K)
          (p := testPlacement Q E.placement α)).2 u v
      | exact (projectiveEntries_neg Q (projectiveEntries_identity Q (K := K)
          (p := testPlacement Q E.placement α))).2 u v

omit [Fintype V] in
omit [DecidableEq A] [DecidableEq I] in
lemma inverseTwistHomotopy_degree (E : BasedComplex Q (K := K) I) (α : V) :
    MapDegree Q (inverseTwistPlacement Q E α) (inverseTwistPlacement Q E α) (-1) 0
      (inverseTwistHomotopy Q E α) := by
  intro i j
  rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v
  all_goals try exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩
  · by_cases h : u = v
    · subst v
      simp only [inverseTwistHomotopy, projectiveIdentity, Matrix.diagonal_apply, ite_true]
      constructor
      · intro hc
        apply (hc _).elim
        dsimp only [inverseTwistPlacement, testPlacement]
        omega
      · convert homogeneous_vertexId Q (K := K) α using 1 <;>
          simp [inverseTwistPlacement, testPlacement]
    · simp only [inverseTwistHomotopy, projectiveIdentity, Matrix.diagonal_apply, ite_eq_right h]
      exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩
  · by_cases h : u = v
    · subst v
      simp only [inverseTwistHomotopy, projectiveIdentity, Matrix.diagonal_apply, ite_true]
      constructor
      · intro hc
        apply (hc _).elim
        dsimp only [inverseTwistPlacement, testPlacement]
        omega
      · convert homogeneous_neg Q (homogeneous_vertexId Q (K := K) α) using 1 <;>
          simp [inverseTwistPlacement, testPlacement]
    · simp only [inverseTwistHomotopy, projectiveIdentity, Matrix.diagonal_apply, ite_eq_right h,
        neg_zero]
      exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
