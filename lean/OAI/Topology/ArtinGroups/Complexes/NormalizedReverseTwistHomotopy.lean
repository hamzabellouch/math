import Mathlib
import OAI.Topology.ArtinGroups.Complexes.Identity
import OAI.Topology.ArtinGroups.Complexes.ReverseTwistProjectionCommute

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

noncomputable def normalizedReverseTwistHomotopyEquivalence
    (hn : ∀ a, Q.source a ≠ Q.target a) (E : BasedComplex Q (K := K) I) (α : V) :
    HomotopyEquivalence Q (normalizedReverseTwist Q hn E α) E where
  forward := {
    matrix := reverseTwistProjection Q E α
    entries := by
      rw [normalizedReverseTwist_placement]
      exact reverseTwistProjection_entries Q E α
    degree := by
      rw [normalizedReverseTwist_placement]
      exact reverseTwistProjection_degree Q E α
    commute := by
      rw [normalizedReverseTwist_differential]
      exact reverseTwistProjection_commute Q E α }
  backward := {
    matrix := reverseTwistInjection Q E α
    entries := by
      rw [normalizedReverseTwist_placement]
      exact reverseTwistInjection_entries Q E α
    degree := by
      rw [normalizedReverseTwist_placement]
      exact reverseTwistInjection_degree Q E α
    commute := by
      rw [normalizedReverseTwist_differential]
      exact reverseTwistInjection_commute Q E α }
  sourceHomotopy := reverseTwistHomotopy Q E α
  targetHomotopy := 0
  sourceEntries := by
    rw [normalizedReverseTwist_placement]
    exact reverseTwistHomotopy_entries Q E α
  targetEntries := projectiveEntries_zero Q
  sourceDegree := by
    rw [normalizedReverseTwist_placement]
    exact reverseTwistHomotopy_degree Q E α
  targetDegree := mapDegree_zero Q (-1) 0
  sourceEquation := by
    dsimp only
    rw [normalizedReverseTwist_placement, normalizedReverseTwist_differential]
    exact reverseTwist_sourceEquation Q hn E α
  targetEquation := by
    dsimp only
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
    exact reverseTwist_targetEquation Q E α

noncomputable def negative_positive_homotopyEquivalence
    (hn : ∀ a, Q.source a ≠ Q.target a) (E : BasedComplex Q (K := K) I) (α : V) :
    HomotopyEquivalence Q ((E.positiveTwist Q α).negativeTwist Q α) E := by
  classical
  exact
  (((E.positiveTwist Q α).negativeTwist Q α).reindexHomotopyEquivalence Q
    (reverseTwistIndexEquiv Q hn E α)).trans Q
      (normalizedReverseTwistHomotopyEquivalence Q hn E α)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
