import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.AllEligibleLower
import OAI.Topology.ArtinGroups.Harmonic.CartanCommutingZero

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

abbrev SourceEligibleWithin (P R:Deligne M) :=
  {Q:Deligne M // Q≤R ∧ ∀i∈R.val.1,i∉Q.val.1→SourceEligible M P Q i}

instance sourceEligibleWithinTop (P R:Deligne M) : OrderTop (SourceEligibleWithin M P R) where
  top:=⟨R,le_rfl,fun _ h hn=>(hn h).elim⟩
  le_top:=fun Q=>Q.property.1

lemma sourceEligibleProduct_left (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (A:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x)
    (i:S) (hi:i∈B) :
    SourceEligible M Ref (sourceCosetProductFun M B C hT x A).val i ↔ SourceEligible M Ref A.1.val i := by
  have hn:i∉(sourceCosetProductFun M B C hT x A).val.val.1 ↔i∉A.1.val.val.1:=by
    constructor
    · exact fun h h'=>h (Or.inl h')
    · intro h
      rintro (h'|h')
      · exact h h'
      · exact Set.disjoint_left.mp hd hi (A.2.property.1 h')
  by_cases ho:i∉A.1.val.val.1
  · simp only [SourceEligible,hn,sourceCosetProduct_open_left M B C hT hd hc x A i hi ho]
  · constructor
    · intro h;exact (ho (hn.mp h.2.1)).elim
    · intro h;exact (ho h.2.1).elim

lemma sourceEligibleProduct_right (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (x:Artin M)
    (A:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x)
    (i:S) (hi:i∈C) :
    SourceEligible M Ref (sourceCosetProductFun M B C hT x A).val i ↔ SourceEligible M Ref A.2.val i := by
  have hn:i∉(sourceCosetProductFun M B C hT x A).val.val.1 ↔i∉A.2.val.val.1:=by
    constructor
    · exact fun h h'=>h (Or.inr h')
    · intro h
      rintro (h'|h')
      · exact Set.disjoint_left.mp hd (A.1.property.1 h') hi
      · exact h h'
  by_cases ho:i∉A.2.val.val.1
  · simp only [SourceEligible,hn,sourceCosetProduct_open_right M B C hT hd x A i hi ho]
  · constructor
    · intro h;exact (ho (hn.mp h.2.1)).elim
    · intro h;exact (ho h.2.1).elim

lemma sourceEligibleProduct_condition (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (A:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x) :
    (∀i∈B∪C,i∉(sourceCosetProductFun M B C hT x A).val.val.1→
      SourceEligible M Ref (sourceCosetProductFun M B C hT x A).val i) ↔
    (∀i∈B,i∉A.1.val.val.1→SourceEligible M Ref A.1.val i) ∧
    (∀i∈C,i∉A.2.val.val.1→SourceEligible M Ref A.2.val i) := by
  constructor
  · intro h
    constructor
    · intro i hi ho
      apply (sourceEligibleProduct_left M Ref B C hT hd hc x A i hi).mp
      apply h i (Or.inl hi)
      rintro (ha|ha)
      · exact ho ha
      · exact Set.disjoint_left.mp hd hi (A.2.property.1 ha)
    · intro i hi ho
      apply (sourceEligibleProduct_right M Ref B C hT hd x A i hi).mp
      apply h i (Or.inr hi)
      rintro (ha|ha)
      · exact Set.disjoint_left.mp hd (A.1.property.1 ha) hi
      · exact ho ha
  · rintro ⟨h,h'⟩ i (hi|hi) ho
    · exact (sourceEligibleProduct_left M Ref B C hT hd hc x A i hi).mpr
        (h i hi (fun hh=>ho (Or.inl hh)))
    · exact (sourceEligibleProduct_right M Ref B C hT hd x A i hi).mpr
        (h' i hi (fun hh=>ho (Or.inr hh)))

noncomputable def sourceEligibleProductFun (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (A:SourceEligibleWithin M Ref (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x) ×
      SourceEligibleWithin M Ref (sourceCoset M C (source_spherical_mono M Set.subset_union_right hT) x)) :
    SourceEligibleWithin M Ref (sourceCoset M (B∪C) hT x) := by
  let a:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x:=⟨A.1.val,A.1.property.1⟩
  let b:SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x:=⟨A.2.val,A.2.property.1⟩
  let p:=sourceCosetProductFun M B C hT x (a,b)
  exact ⟨p.val,p.property,(sourceEligibleProduct_condition M Ref B C hT hd hc x (a,b)).mpr
    ⟨A.1.property.2,A.2.property.2⟩⟩

lemma sourceEligibleProductFun_le_iff (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (A D:SourceEligibleWithin M Ref (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x) ×
      SourceEligibleWithin M Ref (sourceCoset M C (source_spherical_mono M Set.subset_union_right hT) x)) :
    sourceEligibleProductFun M Ref B C hT hd hc x A ≤ sourceEligibleProductFun M Ref B C hT hd hc x D ↔ A≤D :=
  sourceCosetProductFun_le_iff M B C hT hd hc x
    (⟨A.1.val,A.1.property.1⟩,⟨A.2.val,A.2.property.1⟩)
    (⟨D.1.val,D.1.property.1⟩,⟨D.2.val,D.2.property.1⟩)

lemma sourceEligibleProductFun_surjective (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M) :
    Function.Surjective (sourceEligibleProductFun M Ref B C hT hd hc x) := by
  intro D
  obtain ⟨⟨a,b⟩,he⟩:=sourceCosetProductFun_surjective M B C hT hd hc x ⟨D.val,D.property.1⟩
  have hprop:∀i∈B∪C,i∉(sourceCosetProductFun M B C hT x (a,b)).val.val.1→
      SourceEligible M Ref (sourceCosetProductFun M B C hT x (a,b)).val i:=by
    rw [he]
    exact D.property.2
  have hh:=(sourceEligibleProduct_condition M Ref B C hT hd hc x (a,b)).mp hprop
  refine ⟨(⟨a.val,a.property,hh.1⟩,⟨b.val,b.property,hh.2⟩),?_⟩
  apply Subtype.ext
  change (sourceCosetProductFun M B C hT x (a,b)).val=D.val
  exact congrArg Subtype.val he

noncomputable def sourceEligibleProduct (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M) :
    (SourceEligibleWithin M Ref (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x) ×
      SourceEligibleWithin M Ref (sourceCoset M C (source_spherical_mono M Set.subset_union_right hT) x)) ≃o
    SourceEligibleWithin M Ref (sourceCoset M (B∪C) hT x) :=
  OrderIso.ofSurjective
    (OrderEmbedding.ofMapLEIff (sourceEligibleProductFun M Ref B C hT hd hc x)
      (sourceEligibleProductFun_le_iff M Ref B C hT hd hc x))
    (sourceEligibleProductFun_surjective M Ref B C hT hd hc x)

noncomputable def sourceEligiblePuncture (P:Deligne M) :
    {Q:SourceEligibleWithin M P P //Q≠⊤} ≃o SourceAllEligibleLower M P where
  toFun Q:=⟨Q.val.val,lt_of_le_of_ne Q.val.property.1 (fun he=>Q.property (Subtype.ext he)),Q.val.property.2⟩
  invFun Q:=⟨⟨Q.val,Q.property.1.le,Q.property.2⟩,by intro he;exact Q.property.1.ne (congrArg Subtype.val he)⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=Iff.rfl

end HarmonicArtin

end OAI
