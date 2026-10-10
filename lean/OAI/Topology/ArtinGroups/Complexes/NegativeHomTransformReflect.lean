import Mathlib
import OAI.Topology.ArtinGroups.Complexes.NormalizedInverseTwistHomotopy
import OAI.Topology.ArtinGroups.Complexes.NormalizedReverseTwistHomotopy
import OAI.Topology.ArtinGroups.Complexes.ReindexHomOperator
import OAI.Topology.ArtinGroups.Complexes.InverseHomMatrix

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

lemma negativeHomTransform_reflect_boundary (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (α : V) (n v : ℤ) {f : Matrix I J (Q.Zigzag K)}
    (hf : ProjectiveEntries Q E.placement F.placement f)
    (hb : negativeHomTransform Q E F α n f ∈
      homBoundaries Q (E.negativeTwist Q α) (F.negativeTwist Q α) n v) :
    f ∈ homBoundaries Q E F n v := by
  have h₁ := (positiveHomOperator Q (E.negativeTwist Q α)
    (F.negativeTwist Q α) α).map_boundaries n v hb
  have h₂ := (reindexHomOperator Q
    ((E.negativeTwist Q α).positiveTwist Q α)
    ((F.negativeTwist Q α).positiveTwist Q α)
    (inverseTwistIndexEquiv Q hn E α) (inverseTwistIndexEquiv Q hn F α)).map_boundaries n v h₁
  have h₃ := (sandwichHomOperator Q
    (normalizedInverseTwistHomotopyEquivalence Q hn E α).backward
    (normalizedInverseTwistHomotopyEquivalence Q hn F α).forward).map_boundaries n v h₂
  change inverseTwistInjection Q E α *
    (positiveHomTransform Q (E.negativeTwist Q α) (F.negativeTwist Q α) α n
      (negativeHomTransform Q E F α n f)).submatrix
      (inverseTwistIndexEquiv Q hn E α) (inverseTwistIndexEquiv Q hn F α) *
      inverseTwistProjection Q F α ∈ homBoundaries Q E F n v at h₃
  rw [inverseHomMatrix_normalized, inverseHomMatrix_extract Q E F α n hf] at h₃
  exact h₃

lemma positiveHomTransform_reflect_boundary (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (α : V) (n v : ℤ) {f : Matrix I J (Q.Zigzag K)}
    (hf : ProjectiveEntries Q E.placement F.placement f)
    (hb : positiveHomTransform Q E F α n f ∈
      homBoundaries Q (E.positiveTwist Q α) (F.positiveTwist Q α) n v) :
    f ∈ homBoundaries Q E F n v := by
  have h₁ := (negativeHomOperator Q (E.positiveTwist Q α)
    (F.positiveTwist Q α) α).map_boundaries n v hb
  have h₂ := (reindexHomOperator Q
    ((E.positiveTwist Q α).negativeTwist Q α)
    ((F.positiveTwist Q α).negativeTwist Q α)
    (reverseTwistIndexEquiv Q hn E α) (reverseTwistIndexEquiv Q hn F α)).map_boundaries n v h₁
  have h₃ := (sandwichHomOperator Q
    (normalizedReverseTwistHomotopyEquivalence Q hn E α).backward
    (normalizedReverseTwistHomotopyEquivalence Q hn F α).forward).map_boundaries n v h₂
  change reverseTwistInjection Q E α *
    (negativeHomTransform Q (E.positiveTwist Q α) (F.positiveTwist Q α) α n
      (positiveHomTransform Q E F α n f)).submatrix
      (reverseTwistIndexEquiv Q hn E α) (reverseTwistIndexEquiv Q hn F α) *
      reverseTwistProjection Q F α ∈ homBoundaries Q E F n v at h₃
  rw [reverseHomMatrix_normalized, reverseHomMatrix_extract Q E F α n hf] at h₃
  exact h₃

lemma negativeHomCohomology_injective (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (α : V) (n v : ℤ) :
    Function.Injective ((negativeHomOperator Q E F α).onCohomology n v) := by
  apply HomOperator.onCohomology_injective
  intro f hf hb
  exact negativeHomTransform_reflect_boundary Q hn E F α n v hf.1.1 hb

lemma positiveHomCohomology_injective (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (α : V) (n v : ℤ) :
    Function.Injective ((positiveHomOperator Q E F α).onCohomology n v) := by
  apply HomOperator.onCohomology_injective
  intro f hf hb
  exact positiveHomTransform_reflect_boundary Q hn E F α n v hf.1.1 hb

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
