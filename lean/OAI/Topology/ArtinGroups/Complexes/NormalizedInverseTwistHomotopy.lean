import Mathlib
import OAI.Topology.ArtinGroups.Complexes.Identity
import OAI.Topology.ArtinGroups.Complexes.InverseTwistIdentity

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

noncomputable def normalizedInverseTwistHomotopyEquivalence
    (hn : ∀ a, Q.source a ≠ Q.target a) (E : BasedComplex Q (K := K) I) (α : V) :
    HomotopyEquivalence Q (normalizedInverseTwist Q hn E α) E where
  forward := {
    matrix := inverseTwistProjection Q E α
    entries := by
      rw [normalizedInverseTwist_placement]
      exact inverseTwistProjection_entries Q E α
    degree := by
      rw [normalizedInverseTwist_placement]
      exact inverseTwistProjection_degree Q E α
    commute := by
      rw [normalizedInverseTwist_differential]
      exact inverseTwistProjection_commute Q E α }
  backward := {
    matrix := inverseTwistInjection Q E α
    entries := by
      rw [normalizedInverseTwist_placement]
      exact inverseTwistInjection_entries Q E α
    degree := by
      rw [normalizedInverseTwist_placement]
      exact inverseTwistInjection_degree Q E α
    commute := by
      rw [normalizedInverseTwist_differential]
      exact inverseTwistInjection_commute Q E α }
  sourceHomotopy := inverseTwistHomotopy Q E α
  targetHomotopy := 0
  sourceEntries := by
    rw [normalizedInverseTwist_placement]
    exact inverseTwistHomotopy_entries Q E α
  targetEntries := projectiveEntries_zero Q
  sourceDegree := by
    rw [normalizedInverseTwist_placement]
    exact inverseTwistHomotopy_degree Q E α
  targetDegree := mapDegree_zero Q (-1) 0
  sourceEquation := by
    dsimp only
    rw [normalizedInverseTwist_placement, normalizedInverseTwist_differential]
    exact inverseTwist_sourceEquation Q hn E α
  targetEquation := by
    dsimp only
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
    exact inverseTwist_targetEquation Q E α

noncomputable def positive_negative_homotopyEquivalence
    (hn : ∀ a, Q.source a ≠ Q.target a) (E : BasedComplex Q (K := K) I) (α : V) :
    HomotopyEquivalence Q ((E.negativeTwist Q α).positiveTwist Q α) E := by
  classical
  exact
  (((E.negativeTwist Q α).positiveTwist Q α).reindexHomotopyEquivalence Q
    (inverseTwistIndexEquiv Q hn E α)).trans Q
      (normalizedInverseTwistHomotopyEquivalence Q hn E α)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
