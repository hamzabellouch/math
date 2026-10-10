import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeEligibleFactor

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

lemma relativeEligible_left_nonempty (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (V:RelativeEligibleWithin M f U cutoff Ref (sourceCoset M (B∪C) hT x)) (i:S) (hi:i∈B) (ho:i∉V.val.val.1) :
    Nonempty {A:RelativeEligibleWithin M f U cutoff Ref
      (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x) //A≠⊤} := by
  obtain ⟨⟨a,_⟩,he⟩:=relativeEligibleProductFun_surjective M f U cutoff Ref B C hT hd hc x V
  refine ⟨a,?_⟩
  intro ha
  have ht:i∈a.val.val.1:=by rw [ha];exact hi
  apply ho
  rw [←he]
  exact Or.inl ht

lemma relativeBlock_allEligible_contractible (P:Deligne M) (B:Set S) (hB:B⊆P.val.1)
    (hc:∀s∈B,∀t∈P.val.1\B,M s t=2) (x:Artin M) (hx:x∈P.val.2)
    (h:ContractibleSpace (OrderWeights
      {V:RelativeEligibleWithin M f U cutoff P (sourceCoset M B (source_spherical_mono M hB P.property.1) x) //V≠⊤})) :
    ContractibleSpace (OrderWeights (RelativeAllEligibleLower M f U cutoff P)) := by
  let C:=P.val.1\B
  have hBC:B∪C=P.val.1:=Set.union_sdiff_cancel hB
  have hT:IsSpherical M (B∪C):=by rw [hBC];exact P.property.1
  have hd:Disjoint B C:=Set.disjoint_left.mpr (fun _ h h'=>h'.2 h)
  have he:sourceCoset M (B∪C) hT x=P:=by
    simpa only [hBC] using sourceCoset_eq M P x hx
  have hh:=relativeEligibleProduct_contractible M f U cutoff P B C hT hd hc x h
  rw [he] at hh
  exact (weightHomeomorph (relativeEligiblePuncture M f U cutoff P)).contractibleSpace_iff.mp hh

lemma relativeBlock_eligible_nonempty (P:Deligne M) (B:Set S) (hB:B⊆P.val.1)
    (hc:∀s∈B,∀t∈P.val.1\B,M s t=2) (x:Artin M) (hx:x∈P.val.2)
    (V:RelativeAllEligibleLower M f U cutoff P) (i:S) (hi:i∈B) (ho:i∉V.val.val.1) :
    Nonempty {A:RelativeEligibleWithin M f U cutoff P
      (sourceCoset M B (source_spherical_mono M hB P.property.1) x) //A≠⊤} := by
  let C:=P.val.1\B
  have hBC:B∪C=P.val.1:=Set.union_sdiff_cancel hB
  have hT:IsSpherical M (B∪C):=by rw [hBC];exact P.property.1
  have hd:Disjoint B C:=Set.disjoint_left.mpr (fun _ h h'=>h'.2 h)
  have he:sourceCoset M (B∪C) hT x=P:=by simpa only [hBC] using sourceCoset_eq M P x hx
  let W:RelativeEligibleWithin M f U cutoff P (sourceCoset M (B∪C) hT x):=
    ⟨V.val,by rw [he];exact ⟨V.property.1.le,V.property.2⟩⟩
  exact relativeEligible_left_nonempty M f U cutoff P B C hT hd hc x W i hi ho

lemma pointedBlock_vector (P:Deligne M) (B:Set S) (hB:B⊆P.val.1)
    (hc:∀s∈B,∀t∈P.val.1\B,M s t=2) (x:Artin M) (hx:x∈P.val.2) (q:ℤ) :
    ∀i∈B,pointedCosetVector M f (sourceCoset M B (source_spherical_mono M hB P.property.1) x) q (.inl i)=
      pointedCosetVector M f P q (.inl i) := by
  have hBC:B∪(P.val.1\B)=P.val.1:=Set.union_sdiff_cancel hB
  have hT:IsSpherical M (B∪(P.val.1\B)):=by rw [hBC];exact P.property.1
  have he:sourceCoset M (B∪(P.val.1\B)) hT x=P:=by simpa only [hBC] using sourceCoset_eq M P x hx
  intro i hi
  simpa only [he] using pointedCosetVector_block M f B (P.val.1\B) hT hc x q i hi


end HarmonicArtin.ParabolicIntersections

end OAI
