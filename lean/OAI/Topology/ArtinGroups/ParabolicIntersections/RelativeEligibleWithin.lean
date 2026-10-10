import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeAllEligible
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCosetProduct

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open Simplicial CategoryTheory
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

abbrev RelativeEligibleWithin (P R:Deligne M) :=
  {Q:Deligne M // Q≤R ∧ ∀i∈R.val.1,i∉Q.val.1→RelativeEligible M f U cutoff P Q i}

instance relativeEligibleWithinTop (P R:Deligne M) : OrderTop (RelativeEligibleWithin M f U cutoff P R) where
  top:=⟨R,le_rfl,fun _ h hn=>(hn h).elim⟩
  le_top:=fun Q=>Q.property.1

lemma relativeEligibleProduct_left (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (A:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x)
    (i:S) (hi:i∈B) :
    RelativeEligible M f U cutoff Ref (sourceCosetProductFun M B C hT x A).val i ↔ RelativeEligible M f U cutoff Ref A.1.val i := by
  have hn:i∉(sourceCosetProductFun M B C hT x A).val.val.1 ↔i∉A.1.val.val.1:=by
    constructor
    · exact fun h h'=>h (Or.inl h')
    · intro h
      rintro (h'|h')
      · exact h h'
      · exact Set.disjoint_left.mp hd hi (A.2.property.1 h')
  by_cases ho:i∉A.1.val.val.1
  · have he (k:ℕ) : pointedProfile M f (sourceCosetProductFun M B C hT x A).val cutoff k (.inl i) =
        pointedProfile M f A.1.val cutoff k (.inl i) :=
        pointedCosetProduct_open_left M f B C hT hd hc x A i hi ho (cutoff+k)
    simp only [RelativeEligible,hn,he]
  · constructor
    · intro h;exact (ho (hn.mp h.2.1)).elim
    · intro h;exact (ho h.2.1).elim

lemma relativeEligibleProduct_right (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (x:Artin M)
    (A:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x)
    (i:S) (hi:i∈C) :
    RelativeEligible M f U cutoff Ref (sourceCosetProductFun M B C hT x A).val i ↔ RelativeEligible M f U cutoff Ref A.2.val i := by
  have hn:i∉(sourceCosetProductFun M B C hT x A).val.val.1 ↔i∉A.2.val.val.1:=by
    constructor
    · exact fun h h'=>h (Or.inr h')
    · intro h
      rintro (h'|h')
      · exact Set.disjoint_left.mp hd (A.1.property.1 h') hi
      · exact h h'
  by_cases ho:i∉A.2.val.val.1
  · have he (k:ℕ) : pointedProfile M f (sourceCosetProductFun M B C hT x A).val cutoff k (.inl i) =
        pointedProfile M f A.2.val cutoff k (.inl i) :=
        pointedCosetProduct_open_right M f B C hT hd x A i hi ho (cutoff+k)
    simp only [RelativeEligible,hn,he]
  · constructor
    · intro h;exact (ho (hn.mp h.2.1)).elim
    · intro h;exact (ho h.2.1).elim

lemma relativeEligibleProduct_condition (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (A:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x) :
    (∀i∈B∪C,i∉(sourceCosetProductFun M B C hT x A).val.val.1→
      RelativeEligible M f U cutoff Ref (sourceCosetProductFun M B C hT x A).val i) ↔
    (∀i∈B,i∉A.1.val.val.1→RelativeEligible M f U cutoff Ref A.1.val i) ∧
    (∀i∈C,i∉A.2.val.val.1→RelativeEligible M f U cutoff Ref A.2.val i) := by
  constructor
  · intro h
    constructor
    · intro i hi ho
      apply (relativeEligibleProduct_left M f U cutoff Ref B C hT hd hc x A i hi).mp
      apply h i (Or.inl hi)
      rintro (ha|ha)
      · exact ho ha
      · exact Set.disjoint_left.mp hd hi (A.2.property.1 ha)
    · intro i hi ho
      apply (relativeEligibleProduct_right M f U cutoff Ref B C hT hd x A i hi).mp
      apply h i (Or.inr hi)
      rintro (ha|ha)
      · exact Set.disjoint_left.mp hd (A.1.property.1 ha) hi
      · exact ho ha
  · rintro ⟨h,h'⟩ i (hi|hi) ho
    · exact (relativeEligibleProduct_left M f U cutoff Ref B C hT hd hc x A i hi).mpr
        (h i hi (fun hh=>ho (Or.inl hh)))
    · exact (relativeEligibleProduct_right M f U cutoff Ref B C hT hd x A i hi).mpr
        (h' i hi (fun hh=>ho (Or.inr hh)))

noncomputable def relativeEligibleProductFun (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (A:RelativeEligibleWithin M f U cutoff Ref (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x) ×
      RelativeEligibleWithin M f U cutoff Ref (sourceCoset M C (source_spherical_mono M Set.subset_union_right hT) x)) :
    RelativeEligibleWithin M f U cutoff Ref (sourceCoset M (B∪C) hT x) := by
  let a:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x:=⟨A.1.val,A.1.property.1⟩
  let b:SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x:=⟨A.2.val,A.2.property.1⟩
  let p:=sourceCosetProductFun M B C hT x (a,b)
  exact ⟨p.val,p.property,(relativeEligibleProduct_condition M f U cutoff Ref B C hT hd hc x (a,b)).mpr
    ⟨A.1.property.2,A.2.property.2⟩⟩

lemma relativeEligibleProductFun_le_iff (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (A D:RelativeEligibleWithin M f U cutoff Ref (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x) ×
      RelativeEligibleWithin M f U cutoff Ref (sourceCoset M C (source_spherical_mono M Set.subset_union_right hT) x)) :
    relativeEligibleProductFun M f U cutoff Ref B C hT hd hc x A ≤ relativeEligibleProductFun M f U cutoff Ref B C hT hd hc x D ↔ A≤D :=
  sourceCosetProductFun_le_iff M B C hT hd hc x
    (⟨A.1.val,A.1.property.1⟩,⟨A.2.val,A.2.property.1⟩)
    (⟨D.1.val,D.1.property.1⟩,⟨D.2.val,D.2.property.1⟩)

lemma relativeEligibleProductFun_surjective (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M) :
    Function.Surjective (relativeEligibleProductFun M f U cutoff Ref B C hT hd hc x) := by
  intro D
  obtain ⟨⟨a,b⟩,he⟩:=sourceCosetProductFun_surjective M B C hT hd hc x ⟨D.val,D.property.1⟩
  have hprop:∀i∈B∪C,i∉(sourceCosetProductFun M B C hT x (a,b)).val.val.1→
      RelativeEligible M f U cutoff Ref (sourceCosetProductFun M B C hT x (a,b)).val i:=by
    rw [he]
    exact D.property.2
  have hh:=(relativeEligibleProduct_condition M f U cutoff Ref B C hT hd hc x (a,b)).mp hprop
  refine ⟨(⟨a.val,a.property,hh.1⟩,⟨b.val,b.property,hh.2⟩),?_⟩
  apply Subtype.ext
  change (sourceCosetProductFun M B C hT x (a,b)).val=D.val
  exact congrArg Subtype.val he

noncomputable def relativeEligibleProduct (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M) :
    (RelativeEligibleWithin M f U cutoff Ref (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x) ×
      RelativeEligibleWithin M f U cutoff Ref (sourceCoset M C (source_spherical_mono M Set.subset_union_right hT) x)) ≃o
    RelativeEligibleWithin M f U cutoff Ref (sourceCoset M (B∪C) hT x) :=
  OrderIso.ofSurjective
    (OrderEmbedding.ofMapLEIff (relativeEligibleProductFun M f U cutoff Ref B C hT hd hc x)
      (relativeEligibleProductFun_le_iff M f U cutoff Ref B C hT hd hc x))
    (relativeEligibleProductFun_surjective M f U cutoff Ref B C hT hd hc x)

noncomputable def relativeEligiblePuncture (P:Deligne M) :
    {Q:RelativeEligibleWithin M f U cutoff P P //Q≠⊤} ≃o RelativeAllEligibleLower M f U cutoff P where
  toFun Q:=⟨Q.val.val,lt_of_le_of_ne Q.val.property.1 (fun he=>Q.property (Subtype.ext he)),Q.val.property.2⟩
  invFun Q:=⟨⟨Q.val,Q.property.1.le,Q.property.2⟩,by intro he;exact Q.property.1.ne (congrArg Subtype.val he)⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=Iff.rfl


end HarmonicArtin.ParabolicIntersections

end OAI
