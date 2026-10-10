import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.EligibleFactor

namespace OAI

namespace HarmonicArtin
open CategoryTheory Simplicial ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceEligible_left_nonempty (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (V:SourceEligibleWithin M Ref (sourceCoset M (B∪C) hT x)) (i:S) (hi:i∈B) (ho:i∉V.val.val.1) :
    Nonempty {A:SourceEligibleWithin M Ref
      (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x) //A≠⊤} := by
  obtain ⟨⟨a,_⟩,he⟩:=sourceEligibleProductFun_surjective M Ref B C hT hd hc x V
  refine ⟨a,?_⟩
  intro ha
  have ht:i∈a.val.val.1:=by rw [ha];exact hi
  apply ho
  rw [←he]
  exact Or.inl ht

lemma sourceBlock_allEligible_contractible (P:Deligne M) (B:Set S) (hB:B⊆P.val.1)
    (hc:∀s∈B,∀t∈P.val.1\B,M s t=2) (x:Artin M) (hx:x∈P.val.2)
    (h:ContractibleSpace (OrderWeights
      {V:SourceEligibleWithin M P (sourceCoset M B (source_spherical_mono M hB P.property.1) x) //V≠⊤})) :
    ContractibleSpace (OrderWeights (SourceAllEligibleLower M P)) := by
  let C:=P.val.1\B
  have hBC:B∪C=P.val.1:=Set.union_sdiff_cancel hB
  have hT:IsSpherical M (B∪C):=by rw [hBC];exact P.property.1
  have hd:Disjoint B C:=Set.disjoint_left.mpr (fun _ h h'=>h'.2 h)
  have he:sourceCoset M (B∪C) hT x=P:=by
    simpa only [hBC] using sourceCoset_eq M P x hx
  have hh:=sourceEligibleProduct_contractible M P B C hT hd hc x h
  rw [he] at hh
  exact (weightHomeomorph (sourceEligiblePuncture M P)).contractibleSpace_iff.mp hh

lemma sourceBlock_eligible_nonempty (P:Deligne M) (B:Set S) (hB:B⊆P.val.1)
    (hc:∀s∈B,∀t∈P.val.1\B,M s t=2) (x:Artin M) (hx:x∈P.val.2)
    (V:SourceAllEligibleLower M P) (i:S) (hi:i∈B) (ho:i∉V.val.val.1) :
    Nonempty {A:SourceEligibleWithin M P
      (sourceCoset M B (source_spherical_mono M hB P.property.1) x) //A≠⊤} := by
  let C:=P.val.1\B
  have hBC:B∪C=P.val.1:=Set.union_sdiff_cancel hB
  have hT:IsSpherical M (B∪C):=by rw [hBC];exact P.property.1
  have hd:Disjoint B C:=Set.disjoint_left.mpr (fun _ h h'=>h'.2 h)
  have he:sourceCoset M (B∪C) hT x=P:=by simpa only [hBC] using sourceCoset_eq M P x hx
  let W:SourceEligibleWithin M P (sourceCoset M (B∪C) hT x):=
    ⟨V.val,by rw [he];exact ⟨V.property.1.le,V.property.2⟩⟩
  exact sourceEligible_left_nonempty M P B C hT hd hc x W i hi ho

lemma sourceBlock_vector (P:Deligne M) (B:Set S) (hB:B⊆P.val.1)
    (hc:∀s∈B,∀t∈P.val.1\B,M s t=2) (x:Artin M) (hx:x∈P.val.2) (q:ℤ) :
    ∀i∈B,sourceCosetVector M (sourceCoset M B (source_spherical_mono M hB P.property.1) x) q (.inl i)=
      sourceCosetVector M P q (.inl i) := by
  have hBC:B∪(P.val.1\B)=P.val.1:=Set.union_sdiff_cancel hB
  have hT:IsSpherical M (B∪(P.val.1\B)):=by rw [hBC];exact P.property.1
  have he:sourceCoset M (B∪(P.val.1\B)) hT x=P:=by simpa only [hBC] using sourceCoset_eq M P x hx
  intro i hi
  simpa only [he] using sourceCosetVector_block M B (P.val.1\B) hT hc x q i hi

end HarmonicArtin

end OAI
