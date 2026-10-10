import Mathlib
import OAI.Topology.ArtinGroups.Complexes.InverseTwistPlacement

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

noncomputable def reverseTwistProjection (E : BasedComplex Q (K := K) I) (α : V) :
    Matrix (InverseTwistIndex Q E α) I (Q.Zigzag K)
  | .inr (.inr (.inl u)), j => -evaluationMatrix Q E.placement α u j
  | .inr (.inr (.inr (.inl i))), j => projectiveIdentity Q E.placement i j
  | _, _ => 0

noncomputable def reverseTwistInjection (E : BasedComplex Q (K := K) I) (α : V) :
    Matrix I (InverseTwistIndex Q E α) (Q.Zigzag K)
  | i, .inr (.inl u) => coevaluationMatrix Q E.placement α i u
  | i, .inr (.inr (.inr (.inl j))) => projectiveIdentity Q E.placement i j
  | _, _ => 0

noncomputable def reverseTwistHomotopy (E : BasedComplex Q (K := K) I) (α : V) :
    Matrix (InverseTwistIndex Q E α) (InverseTwistIndex Q E α) (Q.Zigzag K) :=
  -inverseTwistHomotopy Q E α

lemma reverseTwistProjection_entries (E : BasedComplex Q (K := K) I) (α : V) :
    ProjectiveEntries Q (inverseTwistPlacement Q E α) E.placement
      (reverseTwistProjection Q E α) := by
  constructor
  · intro i j
    rcases i with u | u | u | i | u
    · exact MulZeroClass.mul_zero _
    · exact MulZeroClass.mul_zero _
    · exact (projectiveEntries_neg Q (evaluation_entries Q E.placement α)).1 u j
    · exact (projectiveEntries_identity Q).1 i j
    · exact MulZeroClass.mul_zero _
  · intro i j
    rcases i with u | u | u | i | u
    · exact MulZeroClass.zero_mul _
    · exact MulZeroClass.zero_mul _
    · exact (projectiveEntries_neg Q (evaluation_entries Q E.placement α)).2 u j
    · exact (projectiveEntries_identity Q).2 i j
    · exact MulZeroClass.zero_mul _

lemma reverseTwistProjection_degree (E : BasedComplex Q (K := K) I) (α : V) :
    MapDegree Q (inverseTwistPlacement Q E α) E.placement 0 0
      (reverseTwistProjection Q E α) := by
  intro i j
  rcases i with u | u | u | i | u
  · exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩
  · exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩
  · exact mapDegree_neg Q (evaluation_degree Q E.placement α) u j
  · exact mapDegree_identity Q i j
  · exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩

lemma reverseTwistInjection_entries (E : BasedComplex Q (K := K) I) (α : V) :
    ProjectiveEntries Q E.placement (inverseTwistPlacement Q E α)
      (reverseTwistInjection Q E α) := by
  constructor
  · intro i j
    rcases j with u | u | u | j | u
    · exact MulZeroClass.mul_zero _
    · exact (coevaluation_entries Q E.placement α).1 i u
    · exact MulZeroClass.mul_zero _
    · exact (projectiveEntries_identity Q).1 i j
    · exact MulZeroClass.mul_zero _
  · intro i j
    rcases j with u | u | u | j | u
    · exact MulZeroClass.zero_mul _
    · exact (coevaluation_entries Q E.placement α).2 i u
    · exact MulZeroClass.zero_mul _
    · exact (projectiveEntries_identity Q).2 i j
    · exact MulZeroClass.zero_mul _

lemma reverseTwistInjection_degree (E : BasedComplex Q (K := K) I) (α : V) :
    MapDegree Q E.placement (inverseTwistPlacement Q E α) 0 0
      (reverseTwistInjection Q E α) := by
  intro i j
  rcases j with u | u | u | j | u
  · exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩
  · exact coevaluation_degree Q E.placement α i u
  · exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩
  · exact mapDegree_identity Q i j
  · exact ⟨fun _ => by trivial, homogeneous_zero Q _⟩

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma reverseTwistHomotopy_entries (E : BasedComplex Q (K := K) I) (α : V) :
    ProjectiveEntries Q (inverseTwistPlacement Q E α) (inverseTwistPlacement Q E α)
      (reverseTwistHomotopy Q E α) :=
  projectiveEntries_neg Q (inverseTwistHomotopy_entries Q E α)

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma reverseTwistHomotopy_degree (E : BasedComplex Q (K := K) I) (α : V) :
    MapDegree Q (inverseTwistPlacement Q E α) (inverseTwistPlacement Q E α) (-1) 0
      (reverseTwistHomotopy Q E α) :=
  mapDegree_neg Q (inverseTwistHomotopy_degree Q E α)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
