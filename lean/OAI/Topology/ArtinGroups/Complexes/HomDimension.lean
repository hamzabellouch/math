import Mathlib
import OAI.Topology.ArtinGroups.Complexes.CorrectionBoundary
import OAI.Topology.ArtinGroups.Complexes.NegativeHomTransformReflect
import OAI.Topology.ArtinGroups.Quivers.OrthogonalVertices

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
universe u
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

instance finiteDimensional : FiniteDimensional K (Q.Zigzag K) :=
  (pathBasis Q (K := K)).finiteDimensional_of_finite

namespace BasedComplex
variable {I J I' J' : Type*} [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
  [DecidableEq I] [DecidableEq J] [DecidableEq I'] [DecidableEq J']

noncomputable def homDimension (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) : ℕ :=
  Module.finrank K (homCohomology Q E F n v)

omit [DecidableEq A] in
lemma HomotopyEquivalence.homDimension_eq {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} {E' : BasedComplex Q (K := K) I'}
    {F' : BasedComplex Q (K := K) J'}
    (e : HomotopyEquivalence Q E E') (f : HomotopyEquivalence Q F F') (n v : ℤ) :
    homDimension Q E F n v = homDimension Q E' F' n v := by
  apply le_antisymm
  · exact LinearMap.finrank_le_finrank_of_injective (e.sandwich_injective Q f n v)
  · exact LinearMap.finrank_le_finrank_of_injective ((e.symm Q).sandwich_injective Q (f.symm Q) n v)

lemma positiveTwist_homDimension (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (α : V) (n v : ℤ) :
    homDimension Q (E.positiveTwist Q α) (F.positiveTwist Q α) n v = homDimension Q E F n v := by
  apply le_antisymm
  · have h := LinearMap.finrank_le_finrank_of_injective
      (negativeHomCohomology_injective Q hn (E.positiveTwist Q α) (F.positiveTwist Q α) α n v)
    change homDimension Q (E.positiveTwist Q α) (F.positiveTwist Q α) n v ≤
      homDimension Q ((E.positiveTwist Q α).negativeTwist Q α)
        ((F.positiveTwist Q α).negativeTwist Q α) n v at h
    rw [(negative_positive_homotopyEquivalence Q hn E α).homDimension_eq Q
      (negative_positive_homotopyEquivalence Q hn F α)] at h
    exact h
  · exact LinearMap.finrank_le_finrank_of_injective (positiveHomCohomology_injective Q hn E F α n v)

lemma negativeTwist_homDimension (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (α : V) (n v : ℤ) :
    homDimension Q (E.negativeTwist Q α) (F.negativeTwist Q α) n v = homDimension Q E F n v := by
  apply le_antisymm
  · have h := LinearMap.finrank_le_finrank_of_injective
      (positiveHomCohomology_injective Q hn (E.negativeTwist Q α) (F.negativeTwist Q α) α n v)
    change homDimension Q (E.negativeTwist Q α) (F.negativeTwist Q α) n v ≤
      homDimension Q ((E.negativeTwist Q α).positiveTwist Q α)
        ((F.negativeTwist Q α).positiveTwist Q α) n v at h
    rw [(positive_negative_homotopyEquivalence Q hn E α).homDimension_eq Q
      (positive_negative_homotopyEquivalence Q hn F α)] at h
    exact h
  · exact LinearMap.finrank_le_finrank_of_injective (negativeHomCohomology_injective Q hn E F α n v)

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
